use std::sync::Arc;

use aws_config::{BehaviorVersion, Region};

use crate::{Result, UbiblkError};

pub fn create_runtime() -> Result<Arc<tokio::runtime::Runtime>> {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map(Arc::new)
        .map_err(|err| UbiblkError::ArchiveError {
            description: format!("Failed to create Tokio runtime for S3 operations: {err}"),
        })
}

pub fn build_s3_client(
    runtime: &Arc<tokio::runtime::Runtime>,
    profile: Option<&str>,
    endpoint: Option<&str>,
    region: Option<&str>,
    credentials: Option<aws_sdk_s3::config::Credentials>,
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
        )
        .expect("client should be created");

        let conf = client.config();
        let endpoint_debug = format!("{:?}", conf);
        assert!(
            endpoint_debug.contains("localhost:9000"),
            "S3 client config should contain the custom endpoint"
        );
    }
}
