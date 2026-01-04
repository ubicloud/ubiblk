use std::sync::Arc;

use log::debug;

use super::ArchiveStore;
use crate::{Result, UbiblkError};

type S3Client = aws_sdk_s3::Client;
type S3ByteStream = aws_sdk_s3::primitives::ByteStream;

pub struct S3Store {
    client: S3Client,
    bucket: String,
    prefix: Option<String>,
    runtime: Arc<tokio::runtime::Runtime>,
}

impl S3Store {
    pub fn new(
        client: S3Client,
        bucket: String,
        prefix: Option<String>,
        runtime: Arc<tokio::runtime::Runtime>,
    ) -> Result<Self> {
        let normalized_prefix = prefix.and_then(|p| {
            let p = p.trim_matches('/');
            if p.is_empty() {
                None
            } else {
                Some(format!("{}/", p))
            }
        });

        Ok(Self {
            client,
            bucket,
            prefix: normalized_prefix,
            runtime,
        })
    }

    fn key_with_prefix(&self, name: &str) -> String {
        if let Some(prefix) = &self.prefix {
            format!("{}{}", prefix, name)
        } else {
            name.to_string()
        }
    }

    fn strip_prefix<'a>(&self, key: &'a str) -> &'a str {
        if let Some(prefix) = &self.prefix {
            key.strip_prefix(prefix).unwrap_or(key)
        } else {
            key
        }
    }

    fn validate_key_name(name: &str) -> Result<()> {
        if name.contains(['/', '\\']) {
            return Err(UbiblkError::ArchiveError {
                description: format!(
                    "Invalid object name '{name}': must not contain path separators"
                ),
            });
        }
        if name == "." || name == ".." {
            return Err(UbiblkError::ArchiveError {
                description: format!("Invalid object name '{name}': cannot be '.' or '..'"),
            });
        }
        if name.is_empty() {
            return Err(UbiblkError::ArchiveError {
                description: "Invalid object name: cannot be empty".to_string(),
            });
        }
        Ok(())
    }

    fn list_objects_page(
        &self,
        continuation_token: Option<String>,
    ) -> Result<(Vec<String>, Option<String>, bool)> {
        let resp = self
            .runtime
            .block_on(async {
                self.client
                    .list_objects_v2()
                    .bucket(&self.bucket)
                    .set_prefix(self.prefix.clone())
                    .set_continuation_token(continuation_token)
                    .send()
                    .await
            })
            .map_err(|e| UbiblkError::ArchiveError {
                description: format!("Failed to list objects in S3: {e}"),
            })?;

        let page_keys = resp
            .contents()
            .iter()
            .filter_map(|o| o.key())
            .map(|k| self.strip_prefix(k).to_string())
            .collect::<Vec<_>>();

        let truncated = resp.is_truncated().unwrap_or(false);
        let next = resp.next_continuation_token().map(|s| s.to_string());

        Ok((page_keys, next, truncated))
    }
}

impl ArchiveStore for S3Store {
    fn put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        debug!("Uploading object to S3: {}", name);
        Self::validate_key_name(name)?;
        let key = self.key_with_prefix(name);

        self.runtime
            .block_on(async {
                self.client
                    .put_object()
                    .bucket(&self.bucket)
                    .key(key)
                    .body(S3ByteStream::from(data.to_vec()))
                    .send()
                    .await
            })
            .map_err(|err| UbiblkError::ArchiveError {
                description: format!("Failed to upload object to S3: {err}"),
            })?;

        Ok(())
    }

    fn get_object(&self, name: &str) -> Result<Vec<u8>> {
        debug!("Fetching object from S3: {}", name);
        Self::validate_key_name(name)?;
        let key = self.key_with_prefix(name);

        let output = self
            .runtime
            .block_on(async {
                self.client
                    .get_object()
                    .bucket(&self.bucket)
                    .key(key)
                    .send()
                    .await
            })
            .map_err(|err| UbiblkError::ArchiveError {
                description: format!("Failed to fetch object from S3: {err}"),
            })?;

        let bytes = self
            .runtime
            .block_on(async { output.body.collect().await })
            .map_err(|err| UbiblkError::ArchiveError {
                description: format!("Failed to read object body: {err}"),
            })?;

        Ok(bytes.to_vec())
    }

    fn list_objects(&self) -> Result<Vec<String>> {
        let mut out = Vec::new();
        let mut continuation_token = None;

        loop {
            let (page, next_continuation_token, truncated) =
                self.list_objects_page(continuation_token)?;
            out.extend(page);

            if !truncated {
                break;
            }
            continuation_token = next_continuation_token;
        }

        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use aws_sdk_s3::{
        operation::{
            get_object::GetObjectOutput, list_objects_v2::ListObjectsV2Output,
            put_object::PutObjectOutput,
        },
        types::Object,
    };
    use aws_smithy_mocks::{mock, mock_client, Rule};

    use super::*;

    fn rt() -> Arc<tokio::runtime::Runtime> {
        Arc::new(
            tokio::runtime::Builder::new_current_thread()
                .enable_io()
                .enable_time()
                .build()
                .unwrap(),
        )
    }

    fn prepare_s3_store(bucket: &str, prefix: Option<&str>, rules: &[Rule]) -> S3Store {
        S3Store::new(
            mock_client!(aws_sdk_s3, rules),
            bucket.to_string(),
            prefix.map(|p| p.to_string()),
            rt(),
        )
        .unwrap()
    }

    #[test]
    fn test_put_object() {
        let put_rule =
            mock!(S3Client::put_object).then_output(|| PutObjectOutput::builder().build());

        let mut store = prepare_s3_store("test-bucket", Some("test-prefix"), &[put_rule]);

        let result = store.put_object("test-object", b"test-data");
        assert!(result.is_ok());
    }

    #[test]
    fn test_get_object() {
        let get_rule = mock!(S3Client::get_object).then_output(|| {
            GetObjectOutput::builder()
                .body(S3ByteStream::from_static(b"hello"))
                .build()
        });

        let store = prepare_s3_store("test-bucket", Some("test-prefix"), &[get_rule]);

        let result = store.get_object("test-object");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), b"hello");
    }

    #[test]
    fn test_list_objects() {
        let list_rule = mock!(S3Client::list_objects_v2).then_output(|| {
            ListObjectsV2Output::builder()
                .contents(Object::builder().key("my/prefix/obj1").build())
                .contents(Object::builder().key("my/prefix/obj2").build())
                .is_truncated(false)
                .build()
        });
        let store = prepare_s3_store("test-bucket", Some("my/prefix"), &[list_rule]);
        let result = store.list_objects();
        assert!(result.is_ok());
        let mut objects = result.unwrap();
        objects.sort();
        assert_eq!(objects, vec!["obj1".to_string(), "obj2".to_string()]);
    }

    #[test]
    fn test_invalid_object_name() {
        let mut store = prepare_s3_store("test-bucket", Some("test-prefix"), &[]);

        let result = store.put_object("invalid/name", b"data");
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("must not contain path separators"));

        let result = store.get_object("..");
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("cannot be '.' or '..'"));

        let result = store.put_object("", b"data");
        assert!(result.is_err());
        assert!(result
            .err()
            .unwrap()
            .to_string()
            .contains("cannot be empty"));
    }

    #[test]
    fn test_no_prefix_handling() {
        let list_rule = mock!(S3Client::list_objects_v2).then_output(|| {
            ListObjectsV2Output::builder()
                .contents(Object::builder().key("obj1").build())
                .contents(Object::builder().key("obj2").build())
                .is_truncated(false)
                .build()
        });
        let store = prepare_s3_store("test-bucket", None, &[list_rule]);

        let result = store.list_objects();
        assert!(result.is_ok());
        let mut objects = result.unwrap();
        objects.sort();
        assert_eq!(objects, vec!["obj1".to_string(), "obj2".to_string()]);
    }

    #[test]
    fn test_paginated_list_objects() {
        let list_rule_page1 = mock!(S3Client::list_objects_v2).then_output(|| {
            ListObjectsV2Output::builder()
                .contents(Object::builder().key("prefix/obj1").build())
                .contents(Object::builder().key("prefix/obj2").build())
                .is_truncated(true)
                .next_continuation_token("token1")
                .build()
        });
        let list_rule_page2 = mock!(S3Client::list_objects_v2).then_output(|| {
            ListObjectsV2Output::builder()
                .contents(Object::builder().key("prefix/obj3").build())
                .is_truncated(false)
                .build()
        });

        let store = prepare_s3_store(
            "test-bucket",
            Some("prefix"),
            &[list_rule_page1, list_rule_page2],
        );

        let result = store.list_objects();
        assert!(result.is_ok());
        let mut objects = result.unwrap();
        objects.sort();
        assert_eq!(
            objects,
            vec!["obj1".to_string(), "obj2".to_string(), "obj3".to_string()]
        );
    }
}
