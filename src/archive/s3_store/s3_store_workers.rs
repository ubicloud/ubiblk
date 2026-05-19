use std::{
    sync::Arc,
    thread::{self, JoinHandle},
    time::Duration,
};

use aws_sdk_s3::error::{DisplayErrorContext, ProvideErrorMetadata};
use bytes::Bytes;
use crossbeam_channel::{Receiver, Sender};

use log::{debug, error, info, warn};

use super::{RetryPolicy, S3ByteStream, S3Client, S3Request, S3Result};
use crate::Result;

/// Parse a Retry-After header value in delta-seconds form.
///
/// RFC 9110 §10.2.3 also permits an HTTP-date form (e.g.
/// `"Wed, 21 Oct 2026 07:28:00 GMT"`). We do not parse that here; if a peer
/// emits it, callers fall back to the exponential schedule. R2 and AWS S3
/// both use delta-seconds in practice.
fn parse_retry_after_seconds(value: &str) -> Option<Duration> {
    value.parse::<u64>().ok().map(Duration::from_secs)
}

/// Sleep duration before the (1-indexed) `attempt`-th retry. Honors a
/// server-supplied Retry-After hint when present; otherwise grows as
/// `initial_backoff * 2^(attempt - 1)`. Either way, clamps to `max_backoff`
/// so a misbehaving peer can't stall the worker indefinitely.
fn retry_delay(policy: &RetryPolicy, attempt: u32, hint: Option<Duration>) -> Duration {
    let exp = {
        let shift = attempt.saturating_sub(1).min(32);
        let base_ms = policy.initial_backoff.as_millis() as u64;
        Duration::from_millis(base_ms.saturating_mul(1u64 << shift))
    };
    hint.unwrap_or(exp).min(policy.max_backoff)
}

fn format_s3_error<E>(operation: &str, key: &str, err: &E, status: Option<u16>) -> String
where
    E: ProvideErrorMetadata + std::error::Error + 'static,
{
    let mut msg = format!("{operation} failed for key '{key}': {err}");
    if let Some(status) = status {
        msg.push_str(&format!(" (status={status})"));
    }
    let meta = err.meta();
    if let Some(code) = meta.code() {
        msg.push_str(&format!(" code={code}"));
    }
    if let Some(message) = meta.message() {
        msg.push_str(&format!(" message={message:?}"));
    }
    msg.push_str(&format!(" — {}", DisplayErrorContext(err)));
    msg
}

struct WorkerContext {
    client: S3Client,
    bucket: Arc<String>,
    retry: RetryPolicy,
}

pub(super) fn spawn_workers(
    client: S3Client,
    bucket: Arc<String>,
    mut worker_threads: usize,
    retry: RetryPolicy,
    request_rx: Receiver<S3Request>,
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

    for i in 0..worker_threads {
        let ctx = WorkerContext {
            client: S3Client::from_conf(client_config.clone()),
            bucket: Arc::clone(&bucket),
            retry,
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
    match req {
        S3Request::Put { name, key, data } => {
            debug!("Uploading object to S3: {}", name);
            // Vec<u8> -> Bytes is O(1) and lets retry attempts share the buffer
            // via cheap refcount clones.
            let body = Bytes::from(data);
            let result = upload_object(ctx, &key, body).await;
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
    }
}

async fn upload_object(ctx: &WorkerContext, key: &str, body: Bytes) -> Result<()> {
    let mut attempt: u32 = 0;
    let err = loop {
        attempt += 1;
        let send_result = ctx
            .client
            .put_object()
            .bucket(ctx.bucket.as_str())
            .key(key)
            .body(S3ByteStream::from(body.clone()))
            .send()
            .await;
        let err = match send_result {
            Ok(_) => return Ok(()),
            Err(e) => e,
        };
        let raw = err.raw_response();
        let retryable = matches!(
            raw.map(|r| r.status().as_u16()),
            Some(408) | Some(429) | Some(500..=599) | None
        );
        if !retryable || attempt >= ctx.retry.max_attempts {
            break err;
        }
        let hint = raw
            .and_then(|r| r.headers().get("retry-after"))
            .and_then(parse_retry_after_seconds);
        let delay = retry_delay(&ctx.retry, attempt, hint);
        warn!(
            "S3 PutObject for {} failed (attempt {}/{}), retrying in {:?}: {}",
            key,
            attempt,
            ctx.retry.max_attempts,
            delay,
            DisplayErrorContext(&err)
        );
        tokio::time::sleep(delay).await;
    };
    let status = err.raw_response().map(|r| r.status().as_u16());
    Err(crate::ubiblk_error!(ArchiveError {
        description: format_s3_error("PutObject", key, &err, status),
    }))
}

async fn fetch_object(ctx: &WorkerContext, key: &str) -> Result<Vec<u8>> {
    let mut attempt: u32 = 0;
    let output = loop {
        attempt += 1;
        let send_result = ctx
            .client
            .get_object()
            .bucket(ctx.bucket.as_str())
            .key(key)
            .send()
            .await;
        let err = match send_result {
            Ok(o) => break o,
            Err(e) => e,
        };
        let raw = err.raw_response();
        let retryable = matches!(
            raw.map(|r| r.status().as_u16()),
            Some(408) | Some(429) | Some(500..=599) | None
        );
        if !retryable || attempt >= ctx.retry.max_attempts {
            let status = raw.map(|r| r.status().as_u16());
            return Err(crate::ubiblk_error!(ArchiveError {
                description: format_s3_error("GetObject", key, &err, status),
            }));
        }
        let hint = raw
            .and_then(|r| r.headers().get("retry-after"))
            .and_then(parse_retry_after_seconds);
        let delay = retry_delay(&ctx.retry, attempt, hint);
        warn!(
            "S3 GetObject for {} failed (attempt {}/{}), retrying in {:?}: {}",
            key,
            attempt,
            ctx.retry.max_attempts,
            delay,
            DisplayErrorContext(&err)
        );
        tokio::time::sleep(delay).await;
    };

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

    use aws_sdk_s3::error::ErrorMetadata;
    use aws_sdk_s3::operation::{get_object::GetObjectOutput, put_object::PutObjectOutput};
    use aws_smithy_mocks::{mock, mock_client, Rule};
    use crossbeam_channel::unbounded;

    use super::*;

    #[derive(Debug)]
    struct FakeServiceError {
        meta: ErrorMetadata,
    }

    impl std::fmt::Display for FakeServiceError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("fake service error")
        }
    }

    impl std::error::Error for FakeServiceError {}

    impl ProvideErrorMetadata for FakeServiceError {
        fn meta(&self) -> &ErrorMetadata {
            &self.meta
        }
    }

    fn policy(max_attempts: u32, initial_ms: u64, max_ms: u64) -> RetryPolicy {
        RetryPolicy {
            max_attempts,
            initial_backoff: Duration::from_millis(initial_ms),
            max_backoff: Duration::from_millis(max_ms),
        }
    }

    #[test]
    fn parse_retry_after_only_accepts_delta_seconds() {
        assert_eq!(parse_retry_after_seconds("5"), Some(Duration::from_secs(5)));
        // HTTP-date form is unsupported and currently falls back to the
        // exponential schedule.
        assert_eq!(
            parse_retry_after_seconds("Wed, 21 Oct 2026 07:28:00 GMT"),
            None
        );
    }

    #[test]
    fn retry_delay_grows_clamps_and_honors_hint() {
        let p = policy(5, 1_000, 10_000);
        // Exponential growth: initial * 2^(n-1).
        assert_eq!(retry_delay(&p, 1, None), Duration::from_millis(1_000));
        assert_eq!(retry_delay(&p, 2, None), Duration::from_millis(2_000));
        assert_eq!(retry_delay(&p, 3, None), Duration::from_millis(4_000));
        // Capped at max_backoff once 2^(n-1) overshoots.
        assert_eq!(retry_delay(&p, 5, None), Duration::from_millis(10_000));
        // Server hint takes precedence over the exponential schedule,
        // but is still clamped by max_backoff.
        assert_eq!(
            retry_delay(&p, 1, Some(Duration::from_secs(3))),
            Duration::from_secs(3)
        );
        assert_eq!(
            retry_delay(&p, 1, Some(Duration::from_secs(86_400))),
            Duration::from_millis(10_000)
        );
    }

    #[test]
    fn format_s3_error_includes_status_code_and_message() {
        let err = FakeServiceError {
            meta: ErrorMetadata::builder()
                .code("SlowDown")
                .message("Please reduce your request rate.")
                .build(),
        };
        let msg = format_s3_error("PutObject", "data/abc", &err, Some(503));
        assert!(msg.contains("PutObject"), "missing op: {msg}");
        assert!(msg.contains("data/abc"), "missing key: {msg}");
        assert!(msg.contains("status=503"), "missing status: {msg}");
        assert!(msg.contains("code=SlowDown"), "missing code: {msg}");
        assert!(
            msg.contains("Please reduce your request rate."),
            "missing message: {msg}"
        );
    }

    #[test]
    fn format_s3_error_handles_missing_metadata() {
        let err = FakeServiceError {
            meta: ErrorMetadata::builder().build(),
        };
        let msg = format_s3_error("GetObject", "metadata.json", &err, None);
        assert!(msg.contains("GetObject"), "missing op: {msg}");
        assert!(msg.contains("metadata.json"), "missing key: {msg}");
        assert!(!msg.contains("status="), "should omit status: {msg}");
        assert!(!msg.contains("code="), "should omit code: {msg}");
    }

    fn spawn_test_workers(
        rules: &[Rule],
    ) -> (Sender<S3Request>, Receiver<S3Result>, Vec<JoinHandle<()>>) {
        // Single attempt so tests don't sleep on transient errors.
        spawn_test_workers_with(rules, policy(1, 1, 1))
    }

    fn spawn_test_workers_with(
        rules: &[Rule],
        retry: RetryPolicy,
    ) -> (Sender<S3Request>, Receiver<S3Result>, Vec<JoinHandle<()>>) {
        let (request_tx, request_rx) = unbounded();
        let (result_tx, result_rx) = unbounded();
        let workers = spawn_workers(
            mock_client!(aws_sdk_s3, rules),
            Arc::new("test-bucket".to_string()),
            1,
            retry,
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

    #[test]
    fn worker_retries_put_on_5xx_then_succeeds() {
        let rule = mock!(S3Client::put_object)
            .sequence()
            .http_status(503, None)
            .output(|| PutObjectOutput::builder().build())
            .build();
        let (request_tx, result_rx, workers) = spawn_test_workers_with(&[rule], policy(3, 1, 1));

        request_tx
            .send(S3Request::Put {
                name: "obj".to_string(),
                key: "prefix/obj".to_string(),
                data: b"payload".to_vec(),
            })
            .expect("send");

        match result_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("result")
        {
            S3Result::Put { name, result } => {
                assert_eq!(name, "obj");
                assert!(
                    result.is_ok(),
                    "expected ok after retry, got {:?}",
                    result.err()
                );
            }
            _ => panic!("expected Put result"),
        }

        drop(request_tx);
        join_workers(workers);
    }

    #[test]
    fn worker_retries_get_on_5xx_then_succeeds() {
        let rule = mock!(S3Client::get_object)
            .sequence()
            .http_status(503, None)
            .output(|| {
                GetObjectOutput::builder()
                    .body(S3ByteStream::from_static(b"hello"))
                    .build()
            })
            .build();
        let (request_tx, result_rx, workers) = spawn_test_workers_with(&[rule], policy(3, 1, 1));

        request_tx
            .send(S3Request::Get {
                name: "obj".to_string(),
                key: "prefix/obj".to_string(),
            })
            .expect("send");

        match result_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("result")
        {
            S3Result::Get { name, result } => {
                assert_eq!(name, "obj");
                assert_eq!(result.expect("expected ok after retry"), b"hello");
            }
            _ => panic!("expected Get result"),
        }

        drop(request_tx);
        join_workers(workers);
    }

    #[test]
    fn worker_gives_up_put_on_permanent_4xx() {
        let rule = mock!(S3Client::put_object)
            .sequence()
            .http_status(403, None)
            .times(10)
            .build();
        let (request_tx, result_rx, workers) = spawn_test_workers_with(&[rule], policy(3, 1, 1));

        request_tx
            .send(S3Request::Put {
                name: "obj".to_string(),
                key: "prefix/obj".to_string(),
                data: b"payload".to_vec(),
            })
            .expect("send");

        match result_rx
            .recv_timeout(Duration::from_secs(2))
            .expect("result")
        {
            S3Result::Put { name, result } => {
                assert_eq!(name, "obj");
                let err = result.expect_err("expected permanent failure");
                let msg = err.to_string();
                assert!(msg.contains("status=403"), "expected 403 in error: {msg}");
            }
            _ => panic!("expected Put result"),
        }

        drop(request_tx);
        join_workers(workers);
    }
}
