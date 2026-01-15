use std::path::PathBuf;

use serde::Deserialize;

#[derive(Debug, Clone, Deserialize, PartialEq)]
#[serde(rename_all = "snake_case")]
pub struct RawStripeSourceConfig {
    pub path: PathBuf,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_yaml::from_str;

    #[test]
    fn test_raw_stripe_source_parsing() {
        let yaml = r#"
        source: raw
        path: "/path/to/image"
        "#;

        let config: super::super::StripeSourceConfig = from_str(yaml).unwrap();
        assert_eq!(
            config,
            super::super::StripeSourceConfig::Raw {
                config: RawStripeSourceConfig {
                    path: PathBuf::from("/path/to/image"),
                }
            }
        );
    }
}
