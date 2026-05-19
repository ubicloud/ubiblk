use std::{sync::Arc, time::Duration};

use aws_config::{BehaviorVersion, Region};
use aws_sdk_s3::config::timeout::TimeoutConfig;

use crate::Result;

#[derive(Debug, Clone, Copy)]
pub struct S3ClientTuning {
    pub connect_timeout_ms: u64,
    pub operation_attempt_timeout_ms: u64,
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
    // Retries are handled in the S3 worker (see `archive::s3_store`) so that we
    // can honor Retry-After hints and apply a deterministic backoff. Disable the
    // SDK's built-in retry to avoid stacking two retry layers.
    builder = builder.retry_config(aws_sdk_s3::config::retry::RetryConfig::disabled());

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

        // SDK retry is disabled — the S3 worker performs retries itself.
        let retry_config = conf.retry_config().expect("retry config present");
        assert_eq!(retry_config.max_attempts(), 1);
    }
}
