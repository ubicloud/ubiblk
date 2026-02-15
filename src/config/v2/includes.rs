use std::path::{Component, Path, PathBuf};

use crate::{ubiblk_error, Result};
use toml::{map::Map, value::Value};

/// A single include directive parsed from the root config.
#[derive(Debug, Clone)]
struct IncludeEntry {
    /// Relative path to the included file (without trailing `?`).
    path: PathBuf,
    /// Whether this include is optional (path had `?` suffix).
    optional: bool,
}

/// Parse the `include` array from a root TOML table.
///
/// Each entry is a string path. Paths ending with `?` mark optional includes
/// that are silently skipped if the file does not exist.
fn parse_include_array(root: &Value) -> Result<Vec<IncludeEntry>> {
    let Some(value) = root.get("include") else {
        return Ok(Vec::new());
    };

    let includes: Vec<String> = value.clone().try_into().map_err(|_| {
        ubiblk_error!(InvalidParameter {
            description: "'include' must be an array of strings".to_string()
        })
    })?;

    includes
        .iter()
        .map(|s| {
            let (path, optional) = match s.strip_suffix('?') {
                Some(p) => (p.to_string(), true),
                None => (s.to_string(), false),
            };
            validate_include_path(&path)?;
            Ok(IncludeEntry {
                path: PathBuf::from(path),
                optional,
            })
        })
        .collect()
}

fn validate_include_path(path: &str) -> Result<()> {
    if path.trim().is_empty() {
        return Err(ubiblk_error!(InvalidParameter {
            description: "include path must not be empty".to_string()
        }));
    }

    let path_buf = Path::new(path);
    if path_buf.is_absolute() {
        return Err(ubiblk_error!(InvalidParameter {
            description: "include path must be relative".to_string()
        }));
    }

    if path_buf.components().any(|component| {
        matches!(
            component,
            Component::ParentDir | Component::Prefix(_) | Component::RootDir
        )
    }) {
        return Err(ubiblk_error!(InvalidParameter {
            description: "include path must be strictly relative and must not contain '..', drive prefixes, or root components".to_string()
        }));
    }

    Ok(())
}

/// Load and merge included TOML files into the root config table.
///
/// Processing:
/// 1. Parse the `include` array from `root`.
/// 2. For each entry, resolve the path relative to `config_dir`.
/// 3. Load the file and parse it as TOML.
/// 4. Reject any included file that itself declares `include` (no nesting).
/// 5. Merge all top-level keys into `root`, rejecting duplicates.
///
/// The `include` key is removed from the returned table after processing.
pub fn resolve_includes(root: Value, config_dir: &Path) -> Result<Value> {
    let entries = parse_include_array(&root)?;

    let Value::Table(mut root_table) = root else {
        return Err(ubiblk_error!(InvalidParameter {
            description: "root config must be a TOML table".to_string()
        }));
    };

    root_table.remove("include");

    for entry in &entries {
        let file_path = config_dir.join(&entry.path);

        let content = match std::fs::read_to_string(&file_path) {
            Ok(c) => c,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound && entry.optional => continue,
            Err(e) => {
                return Err(ubiblk_error!(InvalidParameter {
                    description: format!("include '{:?}': failed to read: {e}", entry.path)
                }));
            }
        };

        let included: Map<String, Value> = toml::from_str(&content).map_err(|e| {
            ubiblk_error!(InvalidParameter {
                description: format!("include '{:?}': parse error: {e}", entry.path)
            })
        })?;

        if included.contains_key("include") {
            return Err(ubiblk_error!(InvalidParameter {
                description: format!(
                    "include '{:?}': nested includes are not allowed",
                    entry.path
                )
            }));
        }

        merge_tables(&mut root_table, &included, &mut Vec::new())?;
    }

    Ok(Value::Table(root_table))
}

/// Merge keys from `addition` into `base` recursively.
fn merge_tables(
    base: &mut Map<String, Value>,
    addition: &Map<String, Value>,
    path: &mut Vec<String>,
) -> Result<()> {
    for (key, value) in addition {
        match (base.get_mut(key), &value) {
            (Some(Value::Table(base_table)), Value::Table(add_table)) => {
                path.push(key.clone());
                merge_tables(base_table, add_table, path)?;
                path.pop();
                continue;
            }
            (Some(Value::Table(_)), _) | (Some(_), Value::Table(_)) => {
                path.push(key.clone());
                return Err(ubiblk_error!(InvalidParameter {
                    description: format!("type mismatch for key '{}' during merge", path.join("."))
                }));
            }
            (Some(_), _) => {
                path.push(key.clone());
                return Err(ubiblk_error!(InvalidParameter {
                    description: format!("duplicate key '{}' during merge", path.join("."))
                }));
            }
            (None, _) => {
                base.insert(key.to_string(), value.clone());
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use tempfile::TempDir;

    fn toml_get_path<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
        let mut current = value;
        for segment in path {
            current = current.get(*segment)?;
        }
        Some(current)
    }

    #[test]
    fn resolve_includes_merges_secrets_and_optional_stripe_source() {
        let dir = TempDir::new().unwrap();
        fs::write(
            dir.path().join("secrets.toml"),
            r#"
                [secrets.xts-key]
                source.inline = "YWJj"
                encoding = "base64"
                [secrets.archive-kek]
                source.env = "ARCHIVE_KEK"
            "#,
        )
        .unwrap();

        fs::write(
            dir.path().join("additional_tuning.toml"),
            r#"
                [tuning]
                queue_size = 4
                write_through = true
            "#,
        )
        .unwrap();

        let root = toml::from_str::<Value>(
            r#"
                include = ["secrets.toml", "stripe_source.toml?", "additional_tuning.toml?"]
                [device]
                device_id = "vm123456"
                data_path = "/path/to/disk.raw"
                metadata_path = "/path/to/metadata"
                vhost_socket = "/path/to/vhost.sock"
                rpc_socket = "/path/to/rpc.sock"
                [tuning]
                num_queues = 4
            "#,
        )
        .unwrap();

        let resolved = resolve_includes(root, dir.path()).unwrap();

        assert!(resolved.get("include").is_none());
        assert!(resolved.get("device").is_some());
        assert!(resolved.get("secrets").is_some());
        assert!(resolved.get("stripe_source").is_none());
        assert!(resolved.get("tuning").is_some());

        assert_eq!(
            toml_get_path(&resolved, &["device", "device_id"]),
            Some(&Value::String("vm123456".to_string()))
        );
        assert_eq!(
            toml_get_path(&resolved, &["device", "data_path"]),
            Some(&Value::String("/path/to/disk.raw".to_string()))
        );
        assert_eq!(
            toml_get_path(&resolved, &["device", "metadata_path"]),
            Some(&Value::String("/path/to/metadata".to_string()))
        );
        assert_eq!(
            toml_get_path(&resolved, &["device", "vhost_socket"]),
            Some(&Value::String("/path/to/vhost.sock".to_string()))
        );
        assert_eq!(
            toml_get_path(&resolved, &["device", "rpc_socket"]),
            Some(&Value::String("/path/to/rpc.sock".to_string()))
        );

        assert_eq!(
            toml_get_path(&resolved, &["secrets", "xts-key", "source", "inline"]),
            Some(&Value::String("YWJj".to_string()))
        );
        assert_eq!(
            toml_get_path(&resolved, &["secrets", "archive-kek", "source", "env"]),
            Some(&Value::String("ARCHIVE_KEK".to_string()))
        );

        assert_eq!(
            toml_get_path(&resolved, &["tuning", "num_queues"]),
            Some(&Value::Integer(4))
        );
        assert_eq!(
            toml_get_path(&resolved, &["tuning", "queue_size"]),
            Some(&Value::Integer(4))
        );
        assert_eq!(
            toml_get_path(&resolved, &["tuning", "write_through"]),
            Some(&Value::Boolean(true))
        );
    }

    #[test]
    fn resolve_includes_rejects_duplicate_key_path() {
        let dir = TempDir::new().unwrap();
        fs::write(
            dir.path().join("secrets.toml"),
            r#"
                [device]
                device_id = "from-include"
            "#,
        )
        .unwrap();

        let root = toml::from_str::<toml::Value>(
            r#"
                include = ["secrets.toml"]
                [device]
                device_id = "vm123456"
            "#,
        )
        .unwrap();

        let error = resolve_includes(root, dir.path()).unwrap_err();
        assert!(format!("{error}").contains("duplicate key 'device.device_id' during merge"));
    }

    #[test]
    fn resolve_includes_rejects_type_mismatch() {
        let dir = TempDir::new().unwrap();
        fs::write(
            dir.path().join("secrets.toml"),
            r#"
                [device]
                device_id = { env = "DEVICE_ID" }
            "#,
        )
        .unwrap();

        let root = toml::from_str::<toml::Value>(
            r#"
                include = ["secrets.toml"]
                [device]
                device_id = "vm123456"
            "#,
        )
        .unwrap();

        let error = resolve_includes(root, dir.path()).unwrap_err();
        assert!(
            format!("{error}").contains("type mismatch for key 'device.device_id' during merge")
        );
    }

    #[test]
    fn resolve_includes_rejects_nested_include_directive() {
        let dir = TempDir::new().unwrap();
        fs::write(
            dir.path().join("secrets.toml"),
            r#"
                include = ["more.toml"]
                [secrets.db]
                source.env = "DB_PASSWORD"
            "#,
        )
        .unwrap();

        let root = toml::from_str::<toml::Value>(
            r#"
                include = ["secrets.toml"]
                [device]
                device_id = "vm123456"
            "#,
        )
        .unwrap();

        let error = resolve_includes(root, dir.path()).unwrap_err();
        assert!(format!("{error}").contains("nested includes are not allowed"));
    }

    #[test]
    fn resolve_includes_rejects_empty_or_non_relative_paths() {
        let root_empty = toml::from_str::<toml::Value>("include = [\"?\"]").unwrap();
        let error_empty = resolve_includes(root_empty, Path::new(".")).unwrap_err();
        assert!(format!("{error_empty}").contains("must not be empty"));

        let root_absolute = toml::from_str::<toml::Value>("include = [\"/etc/passwd\"]").unwrap();
        let error_absolute = resolve_includes(root_absolute, Path::new(".")).unwrap_err();
        assert!(format!("{error_absolute}").contains("must be relative"));

        let root_parent = toml::from_str::<toml::Value>("include = [\"../secret.toml\"]").unwrap();
        let error_parent = resolve_includes(root_parent, Path::new(".")).unwrap_err();
        assert!(format!("{error_parent}").contains("must not contain '..'"));
    }
}
