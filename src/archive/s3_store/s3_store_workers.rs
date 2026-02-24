use std::{
    sync::Arc,
    thread::{self, JoinHandle},
};

use crossbeam_channel::{Receiver, Sender};

use log::{debug, error, info, warn};

use super::{S3ByteStream, S3Client, S3Request, S3Result};
use crate::{utils::s3::UpdatableS3Client, Result};
struct WorkerContext {
    shared_client: Arc<UpdatableS3Client>,
    bucket: Arc<String>,
}

pub(super) fn spawn_workers(
    shared_client: Arc<UpdatableS3Client>,
    bucket: Arc<String>,
    mut worker_threads: usize,
    request_rx: Receiver<S3Request>,
    result_tx: Sender<S3Result>,
) -> Result<Vec<JoinHandle<()>>> {
    if worker_threads < 1 {
        worker_threads = 1;
        warn!("At least one S3 worker thread is required; defaulting to 1");
    }
    if worker_threads > 128 {
        worker_threads = 128;
        warn!("Capping S3 worker threads to maximum of 128");
    }

    let mut workers = Vec::with_capacity(worker_threads);

    for i in 0..worker_threads {
        let ctx = WorkerContext {
            shared_client: Arc::clone(&shared_client),
            bucket: Arc::clone(&bucket),
        };
        let rx = request_rx.clone();
        let tx = result_tx.clone();

        let join_handle = thread::Builder::new()
            .name(format!("s3-worker-{}", i))
            .spawn(move || run_worker_loop(ctx, rx, tx, i))?;
        workers.push(join_handle);
    }

    Ok(workers)
}

fn run_worker_loop(ctx: WorkerContext, rx: Receiver<S3Request>, tx: Sender<S3Result>, id: usize) {
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

    while let Ok(req) = rx.recv() {
        runtime.block_on(async {
            process_request(&ctx, req, &tx).await;
        });
    }

    info!("S3 worker thread {} exiting", id);
}

async fn process_request(ctx: &WorkerContext, req: S3Request, tx: &Sender<S3Result>) {
    // Clone the client before each request so credential updates are picked up
    // and the RwLock is not held across async operations.
    let client = ctx.shared_client.client();
    match req {
        S3Request::Put { name, key, data } => {
            debug!("Uploading object to S3: {}", name);
            let result = upload_object(&client, &ctx.bucket, &key, data).await;
            if let Err(e) = tx.send(S3Result::Put {
                name: name.clone(),
                result,
            }) {
                error!("Failed to send S3Result::Put for {}: {}", name, e);
            }
        }
        S3Request::Get { name, key } => {
            debug!("Fetching object from S3: {}", name);
            let result = fetch_object(&client, &ctx.bucket, &key).await;
            if let Err(e) = tx.send(S3Result::Get {
                name: name.clone(),
                result,
            }) {
                error!("Failed to send S3Result::Get for {}: {}", name, e);
            }
        }
    }
}

async fn upload_object(
    client: &S3Client,
    bucket: &str,
    key: &str,
    data: Vec<u8>,
) -> Result<()> {
    client
        .put_object()
        .bucket(bucket)
        .key(key)
        .body(S3ByteStream::from(data))
        .send()
        .await
        .map_err(|err| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Failed to upload object to S3: {err}"),
            })
        })?;
    Ok(())
}

async fn fetch_object(client: &S3Client, bucket: &str, key: &str) -> Result<Vec<u8>> {
    let output = client
        .get_object()
        .bucket(bucket)
        .key(key)
        .send()
        .await
        .map_err(|err| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Failed to fetch object from S3: {err}"),
            })
        })?;

    let bytes = output.body.collect().await.map_err(|err| {
        crate::ubiblk_error!(ArchiveError {
            description: format!("Failed to read object body: {err}"),
        })
    })?;

    Ok(bytes.to_vec())
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use aws_sdk_s3::operation::{get_object::GetObjectOutput, put_object::PutObjectOutput};
    use aws_smithy_mocks::{mock, mock_client, Rule};
    use crossbeam_channel::unbounded;

    use super::*;

    fn spawn_test_workers(
        rules: &[Rule],
    ) -> (Sender<S3Request>, Receiver<S3Result>, Vec<JoinHandle<()>>) {
        let (request_tx, request_rx) = unbounded();
        let (result_tx, result_rx) = unbounded();
        let shared_client = Arc::new(UpdatableS3Client::new(
            mock_client!(aws_sdk_s3, rules),
            None,
            None,
        ));
        let workers = spawn_workers(
            shared_client,
            Arc::new("test-bucket".to_string()),
            1,
            request_rx,
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
}
