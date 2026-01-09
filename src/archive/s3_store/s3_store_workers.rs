use std::{
    sync::{
        mpsc::{self, Sender},
        Arc, Mutex,
    },
    thread::{self, JoinHandle},
};

use log::{debug, error, warn};

use super::{S3ByteStream, S3Client, S3Request, S3Result};
use crate::{Result, UbiblkError};
struct WorkerContext {
    client: S3Client,
    bucket: Arc<String>,
    prefix: Option<String>,
}

pub(super) fn spawn_workers(
    client: S3Client,
    bucket: Arc<String>,
    prefix: Option<String>,
    mut worker_threads: usize,
    request_rx: Arc<Mutex<mpsc::Receiver<S3Request>>>,
    result_tx: Sender<S3Result>,
) -> Result<Vec<JoinHandle<()>>> {
    let client_config = client.config().clone();

    if worker_threads < 1 {
        worker_threads = 1;
        warn!("At least one S3 worker thread is required; defaulting to 1");
    }
    if worker_threads > 128 {
        worker_threads = 128;
        warn!("Capping S3 worker threads to maximum of 128");
    }

    let mut workers = Vec::with_capacity(worker_threads);

    for _ in 0..worker_threads {
        let ctx = WorkerContext {
            client: S3Client::from_conf(client_config.clone()),
            bucket: Arc::clone(&bucket),
            prefix: prefix.clone(),
        };
        let rx = Arc::clone(&request_rx);
        let tx = result_tx.clone();

        let handle = thread::spawn(move || run_worker_loop(ctx, rx, tx));
        workers.push(handle);
    }

    Ok(workers)
}

fn run_worker_loop(
    ctx: WorkerContext,
    rx: Arc<Mutex<mpsc::Receiver<S3Request>>>,
    tx: Sender<S3Result>,
) {
    let runtime = match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(rt) => rt,
        Err(e) => {
            error!("Critical: Failed to build Tokio runtime for S3 worker: {e}");
            return;
        }
    };

    loop {
        let request = {
            let receiver = match rx.lock() {
                Ok(guard) => guard,
                Err(poisoned_err) => {
                    error!("Critical: S3 request mutex is poisoned: {poisoned_err}");
                    break;
                }
            };
            receiver.recv()
        };

        match request {
            Ok(req) => {
                runtime.block_on(async {
                    process_request(&ctx, req, &tx).await;
                });
            }
            Err(_) => break, // Channel closed
        }
    }
}

async fn process_request(ctx: &WorkerContext, req: S3Request, tx: &Sender<S3Result>) {
    match req {
        S3Request::Put { name, key, data } => {
            debug!("Uploading object to S3: {}", name);
            let result = upload_object(ctx, &key, data).await;
            if let Err(e) = tx.send(S3Result::Put {
                name: name.clone(),
                result,
            }) {
                error!("Failed to send S3Result::Put for {}: {}", name, e);
            }
        }
        S3Request::Get { name, key } => {
            debug!("Fetching object from S3: {}", name);
            let result = fetch_object(ctx, &key).await;
            if let Err(e) = tx.send(S3Result::Get {
                name: name.clone(),
                result,
            }) {
                error!("Failed to send S3Result::Get for {}: {}", name, e);
            }
        }
        S3Request::List { respond_to } => {
            let result = list_objects_async(&ctx.client, &ctx.bucket, &ctx.prefix).await;
            if let Err(e) = respond_to.send(result) {
                error!("Failed to send S3 list response: {}", e);
            }
        }
    }
}

async fn upload_object(ctx: &WorkerContext, key: &str, data: Vec<u8>) -> Result<()> {
    ctx.client
        .put_object()
        .bucket(ctx.bucket.as_str())
        .key(key)
        .body(S3ByteStream::from(data))
        .send()
        .await
        .map_err(|err| UbiblkError::ArchiveError {
            description: format!("Failed to upload object to S3: {err}"),
        })?;
    Ok(())
}

async fn fetch_object(ctx: &WorkerContext, key: &str) -> Result<Vec<u8>> {
    let output = ctx
        .client
        .get_object()
        .bucket(ctx.bucket.as_str())
        .key(key)
        .send()
        .await
        .map_err(|err| UbiblkError::ArchiveError {
            description: format!("Failed to fetch object from S3: {err}"),
        })?;

    let bytes = output
        .body
        .collect()
        .await
        .map_err(|err| UbiblkError::ArchiveError {
            description: format!("Failed to read object body: {err}"),
        })?;

    Ok(bytes.to_vec())
}

async fn list_objects_async(
    client: &S3Client,
    bucket: &str,
    prefix: &Option<String>,
) -> Result<Vec<String>> {
    let mut out = Vec::new();
    let mut continuation_token = None;

    loop {
        let (page, next_continuation_token, truncated) =
            list_objects_page_async(client, bucket, prefix, continuation_token).await?;
        out.extend(page);

        if !truncated {
            break;
        }
        continuation_token = next_continuation_token;
    }

    Ok(out)
}

async fn list_objects_page_async(
    client: &S3Client,
    bucket: &str,
    prefix: &Option<String>,
    continuation_token: Option<String>,
) -> Result<(Vec<String>, Option<String>, bool)> {
    let resp = client
        .list_objects_v2()
        .bucket(bucket)
        .set_prefix(prefix.clone())
        .set_continuation_token(continuation_token)
        .send()
        .await
        .map_err(|e| UbiblkError::ArchiveError {
            description: format!("Failed to list objects in S3: {e}"),
        })?;

    let page_keys = resp
        .contents()
        .iter()
        .filter_map(|o| o.key())
        .map(|k| strip_prefix(prefix, k).to_string())
        .collect::<Vec<_>>();

    let truncated = resp.is_truncated().unwrap_or(false);
    let next = resp.next_continuation_token().map(|s| s.to_string());

    Ok((page_keys, next, truncated))
}

fn strip_prefix<'a>(prefix: &Option<String>, key: &'a str) -> &'a str {
    if let Some(prefix) = prefix.as_deref() {
        key.strip_prefix(prefix).unwrap_or(key)
    } else {
        key
    }
}

#[cfg(test)]
mod tests {
    use mpsc;
    use std::time::Duration;

    use aws_sdk_s3::{
        operation::{
            get_object::GetObjectOutput, list_objects_v2::ListObjectsV2Output,
            put_object::PutObjectOutput,
        },
        types::Object,
    };
    use aws_smithy_mocks::{mock, mock_client, Rule};

    use super::*;

    fn spawn_test_workers(
        rules: &[Rule],
    ) -> (
        mpsc::Sender<S3Request>,
        mpsc::Receiver<S3Result>,
        Vec<JoinHandle<()>>,
    ) {
        let (request_tx, request_rx) = mpsc::channel();
        let (result_tx, result_rx) = mpsc::channel();
        let workers = spawn_workers(
            mock_client!(aws_sdk_s3, rules),
            Arc::new("test-bucket".to_string()),
            Some("prefix/".to_string()),
            1,
            Arc::new(Mutex::new(request_rx)),
            result_tx,
        )
        .expect("failed to spawn workers");
        (request_tx, result_rx, workers)
    }

    fn join_workers(workers: Vec<JoinHandle<()>>) {
        for worker in workers {
            let _ = worker.join();
        }
    }

    #[test]
    fn test_worker_put_and_get() {
        let put_rule =
            mock!(S3Client::put_object).then_output(|| PutObjectOutput::builder().build());
        let get_rule = mock!(S3Client::get_object).then_output(|| {
            GetObjectOutput::builder()
                .body(S3ByteStream::from_static(b"hello"))
                .build()
        });

        let (request_tx, result_rx, workers) = spawn_test_workers(&[put_rule, get_rule]);

        request_tx
            .send(S3Request::Put {
                name: "obj-put".to_string(),
                key: "prefix/obj-put".to_string(),
                data: b"payload".to_vec(),
            })
            .expect("failed to send put request");
        request_tx
            .send(S3Request::Get {
                name: "obj-get".to_string(),
                key: "prefix/obj-get".to_string(),
            })
            .expect("failed to send get request");

        let first = result_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("missing first result");
        let second = result_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("missing second result");

        let mut results = [first, second];
        results.sort_by_key(|result| match result {
            S3Result::Put { name, .. } => name.clone(),
            S3Result::Get { name, .. } => name.clone(),
        });

        match &results[0] {
            S3Result::Get { name, result } => {
                assert_eq!(name, "obj-get");
                assert_eq!(result.as_ref().unwrap(), b"hello");
            }
            _ => panic!("expected get result first after sort"),
        }

        match &results[1] {
            S3Result::Put { name, result } => {
                assert_eq!(name, "obj-put");
                assert!(result.is_ok());
            }
            _ => panic!("expected put result second after sort"),
        }

        drop(request_tx);
        join_workers(workers);
    }

    #[test]
    fn test_worker_list_objects() {
        let list_rule = mock!(S3Client::list_objects_v2).then_output(|| {
            ListObjectsV2Output::builder()
                .contents(Object::builder().key("prefix/a").build())
                .contents(Object::builder().key("prefix/b").build())
                .is_truncated(false)
                .build()
        });

        let (request_tx, _result_rx, workers) = spawn_test_workers(&[list_rule]);
        let (response_tx, response_rx) = mpsc::channel();

        request_tx
            .send(S3Request::List {
                respond_to: response_tx,
            })
            .expect("failed to send list request");

        let result = response_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("missing list response")
            .expect("list response error");

        assert_eq!(result, vec!["a".to_string(), "b".to_string()]);

        drop(request_tx);
        join_workers(workers);
    }
}
