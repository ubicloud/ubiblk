use std::{sync::Arc, time::Duration};

use aws_config::{BehaviorVersion, Region};
use aws_sdk_s3::config::timeout::TimeoutConfig;
use aws_smithy_runtime_api::client::{
    interceptors::context::InterceptorContext,
    retries::{
        classifiers::{ClassifyRetry, RetryAction, RetryClassifierPriority, SharedRetryClassifier},
        ErrorKind,
    },
};

use crate::Result;

#[derive(Debug, Clone, Copy)]
pub struct S3ClientTuning {
    pub connect_timeout_ms: u64,
    pub operation_attempt_timeout_ms: u64,
    pub max_attempts: u32,
    /// When `Some`, retryable responses use a jittered delay instead of the
    /// SDK's exponential backoff. `None` keeps the default backoff.
    pub rate_limited_retry: Option<RateLimitedRetry>,
}

/// Rate-limited-retry delay: a retryable response waits `min_delay + rand[0,
/// jitter)` before the next attempt.
#[derive(Debug, Clone, Copy)]
pub struct RateLimitedRetry {
    pub min_delay: Duration,
    pub jitter: Duration,
}

/// Delays retries of rate-limited S3 responses by a jittered amount.
///
/// The AWS SDK's default backoff is full jitter, so the first retry after a
/// transient `5xx` can fire in well under a second. Some object stores rate-limit
/// rapid retries to the same key and reject a too-fast retry (e.g. with HTTP
/// 429, which the SDK does not retry by default), failing the whole archive.
///
/// For those responses this classifier reports a retry with an explicit delay of
/// `min_delay + rand[0, jitter)`. Because a classifier cannot see the attempt
/// count, the delay does not grow exponentially between attempts — it is a flat,
/// jittered value, which is what avoids the rate limit.
///
/// Only responses carrying an HTTP status are delayed. Client-side timeouts and
/// connection failures (no response) fall back to the SDK's normal backoff.
#[derive(Debug)]
struct RateLimitedRetryClassifier {
    min_delay: Duration,
    jitter: Duration,
}

impl ClassifyRetry for RateLimitedRetryClassifier {
    fn classify_retry(&self, ctx: &InterceptorContext) -> RetryAction {
        let status = ctx.response().map(|r| r.status().as_u16());
        // Transient server errors, and the throttling status some stores return
        // when the same key is retried too quickly.
        if !matches!(status, Some(500 | 502 | 503 | 504 | 429)) {
            return RetryAction::NoActionIndicated;
        }
        let delay = self.min_delay + self.jitter.mul_f64(fastrand::f64());
        RetryAction::retryable_error_with_explicit_delay(ErrorKind::ThrottlingError, delay)
    }

    fn name(&self) -> &'static str {
        "rate-limited-retry"
    }

    fn priority(&self) -> RetryClassifierPriority {
        // Run after the SDK's built-in classifiers so this explicit delay wins
        // over their (equal-priority) exponential-backoff decision on the same
        // response.
        RetryClassifierPriority::run_after(RetryClassifierPriority::transient_error_classifier())
    }
}

pub fn create_runtime() -> Result<Arc<tokio::runtime::Runtime>> {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map(Arc::new)
        .map_err(|err| {
            crate::ubiblk_error!(ArchiveError {
                description: format!("Failed to create Tokio runtime for S3 operations: {err}"),
            })
        })
}

pub fn build_s3_client(
    runtime: &Arc<tokio::runtime::Runtime>,
    profile: Option<&str>,
    endpoint: Option<&str>,
    region: Option<&str>,
    credentials: Option<aws_sdk_s3::config::Credentials>,
    tuning: S3ClientTuning,
) -> Result<aws_sdk_s3::Client> {
    let config = runtime.block_on(async {
        let mut loader = aws_config::defaults(BehaviorVersion::latest());

        if let Some(profile) = profile {
            loader = loader.profile_name(profile);
        }

        if let Some(region) = region {
            loader = loader.region(Region::new(region.to_string()));
        }

        if let Some(credentials) = credentials {
            loader = loader.credentials_provider(credentials);
        }

        loader.load().await
    });

    let mut builder = aws_sdk_s3::config::Builder::from(&config);
    let timeout_config = TimeoutConfig::builder()
        .connect_timeout(Duration::from_millis(tuning.connect_timeout_ms))
        .operation_attempt_timeout(Duration::from_millis(tuning.operation_attempt_timeout_ms))
        .build();
    builder = builder.timeout_config(timeout_config);
    let mut retry_config =
        aws_sdk_s3::config::retry::RetryConfig::standard().with_max_attempts(tuning.max_attempts);
    if let Some(rlr) = tuning.rate_limited_retry {
        // The delay can reach `min_delay + jitter`, which the SDK caps at
        // max_backoff (default 20s). Raise the cap so it never pulls the delay
        // below the configured `min_delay`. Note this cap is global: a
        // `min_delay + jitter` above 20s also raises the ceiling on the SDK's
        // exponential backoff for the no-response retries (timeouts, connection
        // failures) that this classifier leaves on the default schedule.
        let max_delay = rlr.min_delay + rlr.jitter;
        let max_backoff = max_delay.max(retry_config.max_backoff());
        retry_config = retry_config.with_max_backoff(max_backoff);
    }
    builder = builder.retry_config(retry_config);
    if let Some(rlr) = tuning.rate_limited_retry {
        builder.push_retry_classifier(SharedRetryClassifier::new(RateLimitedRetryClassifier {
            min_delay: rlr.min_delay,
            jitter: rlr.jitter,
        }));
    }

    if let Some(endpoint) = endpoint {
        builder = builder.endpoint_url(endpoint);
    }

    Ok(aws_sdk_s3::Client::from_conf(builder.build()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_runtime_runs_async_block() {
        let runtime = create_runtime().expect("runtime should be created");
        let value = runtime.block_on(async { 1 + 1 });
        assert_eq!(value, 2);
    }

    #[test]
    fn test_build_s3_client_with_endpoint_and_credentials() {
        let runtime = create_runtime().expect("runtime should be created");
        let credentials = aws_sdk_s3::config::Credentials::builder()
            .access_key_id("test_access_key")
            .secret_access_key("test_secret_key")
            .provider_name("ubiblk_test")
            .build();

        let client = build_s3_client(
            &runtime,
            Some("default"),
            Some("http://localhost:9000"),
            Some("auto"),
            Some(credentials),
            S3ClientTuning {
                connect_timeout_ms: 5_000,
                operation_attempt_timeout_ms: 20_000,
                max_attempts: 3,
                rate_limited_retry: None,
            },
        )
        .expect("client should be created");

        let conf = client.config();
        let endpoint_debug = format!("{:?}", conf);
        assert!(
            endpoint_debug.contains("localhost:9000"),
            "S3 client config should contain the custom endpoint"
        );

        let timeout_debug = format!("{:?}", conf.timeout_config());
        assert!(
            timeout_debug.contains("5s"),
            "S3 connect timeout should be 5 seconds"
        );
        assert!(
            timeout_debug.contains("20s"),
            "S3 operation attempt timeout should be 20 seconds"
        );

        let retry_debug = format!("{:?}", conf.retry_config());
        assert!(
            retry_debug.contains("max_attempts: 3"),
            "S3 retry config should set max_attempts to 3"
        );
    }

    #[test]
    fn rate_limited_retry_raises_max_backoff_to_fit_the_delay() {
        let runtime = create_runtime().expect("runtime should be created");
        let max_backoff = |min_delay: Duration, jitter: Duration| {
            build_s3_client(
                &runtime,
                None,
                None,
                Some("auto"),
                None,
                S3ClientTuning {
                    connect_timeout_ms: 5_000,
                    operation_attempt_timeout_ms: 20_000,
                    max_attempts: 3,
                    rate_limited_retry: Some(RateLimitedRetry { min_delay, jitter }),
                },
            )
            .expect("client should be created")
            .config()
            .retry_config()
            .expect("retry config present")
            .max_backoff()
        };

        // Small delay: the default 20s cap already fits, so it is unchanged.
        assert_eq!(
            max_backoff(Duration::from_millis(1_500), Duration::from_millis(1_500)),
            Duration::from_secs(20)
        );
        // Large delay: max_backoff is raised to min_delay + jitter so the delay
        // is never capped back below the configured min_delay.
        assert_eq!(
            max_backoff(Duration::from_secs(15), Duration::from_secs(15)),
            Duration::from_secs(30)
        );
    }

    /// Extract the retry delay the classifier requests for a given HTTP status,
    /// or `None` if it declines to retry. The SDK sleeps for exactly this
    /// `retry_after` (an explicit delay overrides its exponential backoff), so
    /// asserting on it is asserting on the actual retry delay.
    fn classified_retry_after(
        classifier: &RateLimitedRetryClassifier,
        status: u16,
    ) -> Option<Duration> {
        use aws_sdk_s3::primitives::SdkBody;
        use aws_smithy_runtime_api::client::interceptors::context::{Input, InterceptorContext};
        use aws_smithy_runtime_api::client::retries::classifiers::RetryReason;
        use aws_smithy_runtime_api::http::{Response, StatusCode};

        let mut ctx = InterceptorContext::new(Input::doesnt_matter());
        ctx.set_response(Response::new(
            StatusCode::try_from(status).unwrap(),
            SdkBody::empty(),
        ));
        match classifier.classify_retry(&ctx) {
            RetryAction::RetryIndicated(RetryReason::RetryableError { retry_after, .. }) => {
                retry_after
            }
            _ => None,
        }
    }

    #[test]
    fn classifier_ignores_non_retryable_responses() {
        use aws_smithy_runtime_api::client::interceptors::context::{Input, InterceptorContext};

        let classifier = RateLimitedRetryClassifier {
            min_delay: Duration::from_millis(500),
            jitter: Duration::from_millis(500),
        };

        // No response yet -> no opinion.
        let ctx = InterceptorContext::new(Input::doesnt_matter());
        assert_eq!(
            classifier.classify_retry(&ctx),
            RetryAction::NoActionIndicated
        );

        // Success / non-transient client errors -> no opinion.
        for status in [200, 301, 400, 403, 404] {
            assert_eq!(
                classified_retry_after(&classifier, status),
                None,
                "status {status} should not be retried"
            );
        }
    }

    // The real check: for every retryable status, the delay the classifier
    // requests (which is what the SDK sleeps for) must stay in `[min_delay,
    // min_delay + jitter)`, across many jitter samples. If the floor were
    // dropped — e.g. the delay became `rand[0, min_delay)` — this fails on
    // essentially the first sample, so >>0.9 of the time.
    #[test]
    fn classifier_delay_stays_in_floor_plus_jitter_window() {
        let min_delay = Duration::from_millis(500);
        let jitter = Duration::from_millis(300);
        let classifier = RateLimitedRetryClassifier { min_delay, jitter };

        let mut min_seen = Duration::MAX;
        let mut max_seen = Duration::ZERO;
        for _ in 0..2000 {
            for status in [500, 502, 503, 504, 429] {
                let delay = classified_retry_after(&classifier, status)
                    .unwrap_or_else(|| panic!("status {status} should be retried with a delay"));
                assert!(
                    delay >= min_delay,
                    "status {status}: delay {delay:?} is below the floor {min_delay:?}"
                );
                assert!(
                    delay < min_delay + jitter,
                    "status {status}: delay {delay:?} exceeds min_delay + jitter"
                );
                min_seen = min_seen.min(delay);
                max_seen = max_seen.max(delay);
            }
        }

        // The floor is a genuine minimum, and the jitter actually spreads the
        // delay above it (not a constant that merely happens to equal min_delay).
        assert!(
            min_seen >= min_delay,
            "floor violated: min was {min_seen:?}"
        );
        assert!(
            max_seen > min_delay,
            "expected jitter above the floor, but max delay was {max_seen:?}"
        );
    }
}
