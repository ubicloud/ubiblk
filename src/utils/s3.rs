use std::sync::{Arc, RwLock};

use aws_config::{BehaviorVersion, Region};
use log::info;

use crate::Result;

type S3Client = aws_sdk_s3::Client;

/// An S3 client wrapper that supports atomic credential updates via RPC.
///
/// Stores the S3 config (not a live client), so each caller can build a fresh
/// S3 client with its own connection pool. This is necessary because each S3
/// worker thread runs its own single-threaded tokio runtime, and connection
/// pools are tied to the runtime that created them.
///
/// When `update_credentials` is called, the stored config is replaced so that
/// subsequent `build_client` calls use the new credentials.
#[derive(Debug)]
pub struct UpdatableS3Client {
    config: RwLock<aws_sdk_s3::Config>,
    endpoint: Option<String>,
    region: Option<String>,
}

impl UpdatableS3Client {
    pub fn new(client: S3Client, endpoint: Option<String>, region: Option<String>) -> Self {
        let config = client.config().clone();
        Self {
            config: RwLock::new(config),
            endpoint,
            region,
        }
    }

    /// Build a new S3 client from the current config. Each caller gets its own
    /// connection pool, safe to use on any tokio runtime.
    pub fn build_client(&self) -> S3Client {
        S3Client::from_conf(self.config.read().unwrap().clone())
    }

    /// Alias for `build_client` for backward compatibility.
    pub fn client(&self) -> S3Client {
        self.build_client()
    }

    /// Atomically replace the S3 config with one using new credentials.
    pub fn update_credentials(
        &self,
        access_key_id: String,
        secret_access_key: String,
        session_token: Option<String>,
    ) -> Result<()> {
        let mut creds_builder = aws_sdk_s3::config::Credentials::builder()
            .access_key_id(access_key_id)
            .secret_access_key(secret_access_key)
            .provider_name("ubiblk_archive");
        if let Some(token) = session_token {
            creds_builder = creds_builder.session_token(token);
        }
        let credentials = creds_builder.build();

        let runtime = create_runtime()?;
        let new_client = build_s3_client(
            &runtime,
            None,
            self.endpoint.as_deref(),
            self.region.as_deref(),
            Some(credentials),
        )?;

        *self.config.write().unwrap() = new_client.config().clone();
        info!("S3 credentials updated successfully");
        Ok(())
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
    fn test_updatable_s3_client_update_credentials() {
        let runtime = create_runtime().expect("runtime should be created");
        let credentials = aws_sdk_s3::config::Credentials::builder()
            .access_key_id("old_key")
            .secret_access_key("old_secret")
            .provider_name("ubiblk_test")
            .build();
        let client = build_s3_client(
            &runtime,
            None,
            Some("http://localhost:9000"),
            Some("auto"),
            Some(credentials),
        )
        .expect("client should be created");

        let updatable = UpdatableS3Client::new(
            client,
            Some("http://localhost:9000".to_string()),
            Some("auto".to_string()),
        );

        // Should succeed
        let result = updatable.update_credentials(
            "new_key".to_string(),
            "new_secret".to_string(),
            Some("session_tok".to_string()),
        );
        assert!(result.is_ok());

        // Client should still be usable
        let _client = updatable.client();
    }

    #[test]
    fn test_updatable_s3_client_without_session_token() {
        let runtime = create_runtime().expect("runtime should be created");
        let client = build_s3_client(&runtime, None, None, None, None)
            .expect("client should be created");

        let updatable = UpdatableS3Client::new(client, None, None);
        let result =
            updatable.update_credentials("key".to_string(), "secret".to_string(), None);
        assert!(result.is_ok());
    }

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
