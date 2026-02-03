use super::ArchiveStore;
use crate::{Result, ResultExt};
use std::{fs, path::PathBuf};

pub struct FileSystemStore {
    base_path: PathBuf,
    finished_puts: Vec<(String, Result<()>)>,
    finished_gets: Vec<(String, Result<Vec<u8>>)>,
}

impl FileSystemStore {
    pub fn new(base_path: PathBuf) -> Result<Self> {
        fs::create_dir_all(&base_path)?;
        Ok(Self {
            base_path,
            finished_puts: Vec::new(),
            finished_gets: Vec::new(),
        })
    }

    fn try_put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        let mut path = self.base_path.clone();
        path.push(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .context(format!("Failed to create dir {}", parent.display()))?;
        }
        fs::write(&path, data).context(format!("Failed to write {}", path.display()))?;
        Ok(())
    }

    fn try_get_object(&self, name: &str) -> Result<Vec<u8>> {
        let mut path = self.base_path.clone();
        path.push(name);
        let data = fs::read(&path).context(format!("Failed to read {}", path.display()))?;
        Ok(data)
    }
}

impl ArchiveStore for FileSystemStore {
    fn start_put_object(&mut self, name: &str, data: Vec<u8>) {
        let result = self.try_put_object(name, &data);
        self.finished_puts.push((name.to_string(), result));
    }

    fn start_get_object(&mut self, name: &str) {
        let result = self.try_get_object(name);
        self.finished_gets.push((name.to_string(), result));
    }

    fn poll_puts(&mut self) -> Vec<(String, Result<()>)> {
        std::mem::take(&mut self.finished_puts)
    }

    fn poll_gets(&mut self) -> Vec<(String, Result<Vec<u8>>)> {
        std::mem::take(&mut self.finished_gets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    use tempfile::tempdir;

    #[test]
    fn test_filesystem_put_and_get() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;
        let object_name = "test_object";
        let object_data = b"Hello, Archive!";
        store.put_object(object_name, object_data, Duration::from_secs(5))?;
        let retrieved_data = store.get_object(object_name, Duration::from_secs(5))?;
        assert_eq!(object_data.to_vec(), retrieved_data);
        Ok(())
    }

    #[test]
    fn test_creates_directory() -> Result<()> {
        let dir = tempdir()?;
        let new_dir = dir.path().join("new_store");
        let _store = FileSystemStore::new(new_dir.clone())?;
        assert!(new_dir.exists() && new_dir.is_dir());
        Ok(())
    }
}
