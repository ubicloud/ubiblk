use std::{sync::Arc, thread::JoinHandle};

use crossbeam_channel::{unbounded, Receiver, Sender};
use log::{debug, error, info};

use super::ArchiveStore;
use crate::Result;
use s3_store_workers::spawn_workers;

type S3Client = aws_sdk_s3::Client;
type S3ByteStream = aws_sdk_s3::primitives::ByteStream;

mod s3_store_workers;

enum S3Request {
    Put {
        name: String,
        key: String,
        data: Vec<u8>,
    },
    Get {
        name: String,
        key: String,
    },
}

enum S3Result {
    Put {
        name: String,
        result: Result<()>,
    },
    Get {
        name: String,
        result: Result<Vec<u8>>,
    },
}

pub struct S3Store {
    prefix: Option<String>,
    request_tx: Option<Sender<S3Request>>,
    result_rx: Receiver<S3Result>,
    finished_puts: Vec<(String, Result<()>)>,
    finished_gets: Vec<(String, Result<Vec<u8>>)>,
    workers: Vec<JoinHandle<()>>,
}

impl S3Store {
    pub fn new(
        client: S3Client,
        bucket: String,
        prefix: Option<String>,
        worker_threads: usize,
    ) -> Result<Self> {
        let normalized_prefix = prefix.and_then(|p| {
            let p = p.trim_matches('/');
            if p.is_empty() {
                None
            } else {
                Some(format!("{}/", p))
            }
        });

        let (request_tx, request_rx) = unbounded();
        let (result_tx, result_rx) = unbounded();
        let bucket = Arc::new(bucket);
        let workers = spawn_workers(
            client,
            Arc::clone(&bucket),
            worker_threads,
            request_rx,
            result_tx,
        )?;

        Ok(Self {
            prefix: normalized_prefix,
            request_tx: Some(request_tx),
            result_rx,
            finished_puts: Vec::new(),
            finished_gets: Vec::new(),
            workers,
        })
    }

    fn drain_results(&mut self) {
        for result in self.result_rx.try_iter() {
            match result {
                S3Result::Put { name, result } => {
                    self.finished_puts.push((name.clone(), result));
                }
                S3Result::Get { name, result } => {
                    self.finished_gets.push((name.clone(), result));
                }
            }
        }
    }
}

impl Drop for S3Store {
    fn drop(&mut self) {
        info!("Shutting down S3Store workers");
        let _ = self.request_tx.take();
        for worker in self.workers.drain(..) {
            if let Err(e) = worker.join() {
                error!("Failed to join S3 worker thread: {:?}", e);
            }
        }
        self.drain_results();
    }
}

impl ArchiveStore for S3Store {
    fn start_put_object(&mut self, name: &str, data: Vec<u8>) {
        debug!("Queueing S3 put object: {}", name);
        let key = key_with_prefix(&self.prefix, name);
        let request = S3Request::Put {
            name: name.to_string(),
            key,
            data,
        };
        if let Some(sender) = self.request_tx.as_ref() {
            if let Err(err) = sender.send(request) {
                self.finished_puts.push((
                    name.to_string(),
                    Err(crate::ubiblk_error!(ArchiveError {
                        description: format!("Failed to enqueue S3 put request: {err}"),
                    })),
                ));
            }
        } else {
            self.finished_puts.push((
                name.to_string(),
                Err(crate::ubiblk_error!(ArchiveError {
                    description: "S3 worker queue is unavailable".to_string(),
                })),
            ));
        }
    }

    fn start_get_object(&mut self, name: &str) {
        debug!("Queueing S3 get object: {}", name);
        let key = key_with_prefix(&self.prefix, name);
        let request = S3Request::Get {
            name: name.to_string(),
            key,
        };
        if let Some(sender) = self.request_tx.as_ref() {
            if let Err(err) = sender.send(request) {
                self.finished_gets.push((
                    name.to_string(),
                    Err(crate::ubiblk_error!(ArchiveError {
                        description: format!("Failed to enqueue S3 get request: {err}"),
                    })),
                ));
            }
        } else {
            self.finished_gets.push((
                name.to_string(),
                Err(crate::ubiblk_error!(ArchiveError {
                    description: "S3 worker queue is unavailable".to_string(),
                })),
            ));
        }
    }

    fn poll_puts(&mut self) -> Vec<(String, Result<()>)> {
        self.drain_results();
        std::mem::take(&mut self.finished_puts)
    }

    fn poll_gets(&mut self) -> Vec<(String, Result<Vec<u8>>)> {
        self.drain_results();
        std::mem::take(&mut self.finished_gets)
    }
}

fn key_with_prefix(prefix: &Option<String>, name: &str) -> String {
    if let Some(prefix) = prefix {
        format!("{}{}", prefix, name)
    } else {
        name.to_string()
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use aws_sdk_s3::operation::{get_object::GetObjectOutput, put_object::PutObjectOutput};
    use aws_smithy_mocks::{mock, mock_client, Rule};

    use super::*;

    fn test_store(request_tx: Option<Sender<S3Request>>) -> S3Store {
        let (_, result_rx) = unbounded();
        S3Store {
            prefix: None,
            request_tx,
            result_rx,
            finished_puts: Vec::new(),
            finished_gets: Vec::new(),
            workers: Vec::new(),
        }
    }

    fn prepare_s3_store(bucket: &str, prefix: Option<&str>, rules: &[Rule]) -> S3Store {
        S3Store::new(
            mock_client!(aws_sdk_s3, rules),
            bucket.to_string(),
            prefix.map(|p| p.to_string()),
            2,
        )
        .unwrap()
    }

    #[test]
    fn test_put_object() {
        let put_rule =
            mock!(S3Client::put_object).then_output(|| PutObjectOutput::builder().build());

        let mut store = prepare_s3_store("test-bucket", Some("test-prefix"), &[put_rule]);

        let result = store.put_object("test-object", b"test-data", Duration::from_secs(5));
        assert!(result.is_ok());
    }

    #[test]
    fn start_put_object_errors_when_queue_missing() {
        let mut store = test_store(None);
        store.start_put_object("object", b"data".to_vec());
        let results = store.poll_puts();
        assert_eq!(results.len(), 1);
        let err = results[0]
            .1
            .as_ref()
            .expect_err("expected error when queue missing");
        assert!(
            err.to_string().contains("S3 worker queue is unavailable"),
            "unexpected error: {err}"
        );
    }

    #[test]
    fn test_get_object() {
        let get_rule = mock!(S3Client::get_object).then_output(|| {
            GetObjectOutput::builder()
                .body(S3ByteStream::from_static(b"hello"))
                .build()
        });

        let mut store = prepare_s3_store("test-bucket", Some("test-prefix"), &[get_rule]);

        let result = store.get_object("test-object", Duration::from_secs(5));
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), b"hello");
    }

    #[test]
    fn start_get_object_errors_when_queue_missing() {
        let mut store = test_store(None);
        store.start_get_object("object");
        let results = store.poll_gets();
        assert_eq!(results.len(), 1);
        let err = results[0]
            .1
            .as_ref()
            .expect_err("expected error when queue missing");
        assert!(
            err.to_string().contains("S3 worker queue is unavailable"),
            "unexpected error: {err}"
        );
    }
}
