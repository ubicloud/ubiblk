use std::{sync::Arc, time::Duration};

use aws_config::{BehaviorVersion, Region};
use aws_sdk_s3::config::timeout::TimeoutConfig;
use aws_smithy_runtime_api::client::{
    interceptors::context::InterceptorContext,
    retries::classifiers::{
        ClassifyRetry, RetryAction, RetryClassifierPriority, SharedRetryClassifier,
    },
};

use crate::Result;

#[derive(Debug, Clone, Copy)]
pub struct S3ClientTuning {
    pub connect_timeout_ms: u64,
    pub operation_attempt_timeout_ms: u64,
    pub max_attempts: u32,
    pub initial_backoff_ms: u64,
    pub max_backoff_ms: u64,
}

/// The SDK's default `HttpStatusCodeClassifier` only marks 500/502/503/504 as
/// retryable. Cloudflare R2 returns HTTP 429 for its per-object rate limit and
/// includes a `Retry-After` header; without this classifier the SDK gives up
/// on the first throttle response.
#[derive(Debug)]
struct Retry429Classifier;

impl ClassifyRetry for Retry429Classifier {
    fn classify_retry(&self, ctx: &InterceptorContext) -> RetryAction {
        let Some(response) = ctx.response() else {
            return RetryAction::NoActionIndicated;
        };
        if response.status().as_u16() != 429 {
            return RetryAction::NoActionIndicated;
        }
        // Honor Retry-After (delta-seconds form) when the server provides it.
        // HTTP-date form is uncommon for S3-compatible peers; if it appears we
        // fall back to the standard exponential schedule.
        let retry_after = response
            .headers()
            .get("retry-after")
            .and_then(|v| v.parse::<u64>().ok())
            .map(Duration::from_secs);
        match retry_after {
            Some(d) => RetryAction::retryable_error_with_explicit_delay(
                aws_smithy_runtime_api::client::retries::ErrorKind::ThrottlingError,
                d,
            ),
            None => RetryAction::throttling_error(),
        }
    }

    fn name(&self) -> &'static str {
        "Retry429"
    }

    fn priority(&self) -> RetryClassifierPriority {
        // Run after the SDK's built-in classifiers so a `ThrottlingError` decision
        // here overrides any equal-priority `transient_error` they might produce
        // on the same 429. Equal-priority ordering is unspecified by the SDK.
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
    let retry_config = aws_sdk_s3::config::retry::RetryConfig::standard()
        .with_max_attempts(tuning.max_attempts)
        .with_initial_backoff(Duration::from_millis(tuning.initial_backoff_ms))
        .with_max_backoff(Duration::from_millis(tuning.max_backoff_ms));
    builder = builder.retry_config(retry_config);
    builder.push_retry_classifier(SharedRetryClassifier::new(Retry429Classifier));

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
                initial_backoff_ms: 2_000,
                max_backoff_ms: 30_000,
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

        let retry_config = conf.retry_config().expect("retry config present");
        assert_eq!(retry_config.max_attempts(), 3);
        assert_eq!(retry_config.initial_backoff(), Duration::from_millis(2_000));
        assert_eq!(retry_config.max_backoff(), Duration::from_millis(30_000));
    }

    #[test]
    fn retry_429_classifier_marks_throttle_response_retryable() {
        use aws_sdk_s3::primitives::SdkBody;
        use aws_smithy_runtime_api::client::interceptors::context::{Input, InterceptorContext};
        use aws_smithy_runtime_api::http::{Response, StatusCode};

        let classifier = Retry429Classifier;

        // No response yet -> no opinion.
        let ctx = InterceptorContext::new(Input::doesnt_matter());
        assert_eq!(
            classifier.classify_retry(&ctx),
            RetryAction::NoActionIndicated
        );

        // 200 -> no opinion.
        let mut ctx = InterceptorContext::new(Input::doesnt_matter());
        ctx.set_response(Response::new(
            StatusCode::try_from(200).unwrap(),
            SdkBody::empty(),
        ));
        assert_eq!(
            classifier.classify_retry(&ctx),
            RetryAction::NoActionIndicated
        );

        // 429 without Retry-After -> throttling retry, no explicit delay.
        let mut ctx = InterceptorContext::new(Input::doesnt_matter());
        ctx.set_response(Response::new(
            StatusCode::try_from(429).unwrap(),
            SdkBody::empty(),
        ));
        assert_eq!(
            classifier.classify_retry(&ctx),
            RetryAction::throttling_error()
        );

        // 429 with Retry-After: 5 -> throttling retry with explicit 5s delay.
        let mut response = Response::new(StatusCode::try_from(429).unwrap(), SdkBody::empty());
        response.headers_mut().append("retry-after", "5");
        let mut ctx = InterceptorContext::new(Input::doesnt_matter());
        ctx.set_response(response);
        assert_eq!(
            classifier.classify_retry(&ctx),
            RetryAction::retryable_error_with_explicit_delay(
                aws_smithy_runtime_api::client::retries::ErrorKind::ThrottlingError,
                Duration::from_secs(5)
            )
        );
    }
}
