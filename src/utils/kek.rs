use crate::{KeyEncryptionCipher, Result, VhostUserBlockError};
use std::{fs::File, path::PathBuf};

pub fn load_kek(path: Option<&PathBuf>, unlink: bool) -> Result<KeyEncryptionCipher> {
    let Some(path) = path else {
        return Ok(KeyEncryptionCipher::default());
    };

    let file = File::open(path)?;
    let kek: KeyEncryptionCipher =
        serde_yaml::from_reader(file).map_err(|e| VhostUserBlockError::InvalidParameter {
            description: format!("Error parsing KEK file {}: {e}", path.display()),
        })?;

    if unlink {
        std::fs::remove_file(path)?;
    }

    Ok(kek)
}
