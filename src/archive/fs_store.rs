use super::ArchiveStore;
use crate::Result;
use std::{fs, path::PathBuf};

pub struct FileSystemStore {
    base_path: PathBuf,
}

impl FileSystemStore {
    pub fn new(base_path: PathBuf) -> Self {
        Self { base_path }
    }
}

impl ArchiveStore for FileSystemStore {
    fn put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        let mut path = self.base_path.clone();
        path.push(name);
        fs::write(path, data)?;
        Ok(())
    }

    fn get_object(&self, name: &str) -> Result<Vec<u8>> {
        let mut path = self.base_path.clone();
        path.push(name);
        let data = fs::read(path)?;
        Ok(data)
    }

    fn list_objects(&self) -> Result<Vec<String>> {
        let mut objects = Vec::new();
        for entry in fs::read_dir(&self.base_path)? {
            let entry = entry?;
            if entry.file_type()?.is_file() {
                if let Some(name) = entry.file_name().to_str() {
                    objects.push(name.to_string());
                }
            }
        }
        Ok(objects)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_filesystem_put_and_get() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf());
        let object_name = "test_object";
        let object_data = b"Hello, Archive!";
        store.put_object(object_name, object_data)?;
        let retrieved_data = store.get_object(object_name)?;
        assert_eq!(object_data.to_vec(), retrieved_data);
        Ok(())
    }

    #[test]
    fn test_filesystem_list_objects() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf());
        let object_names = vec!["obj1", "obj2", "obj3"];
        for name in &object_names {
            store.put_object(name, b"data")?;
        }
        let listed_objects = store.list_objects()?;
        assert_eq!(listed_objects.len(), object_names.len());
        for name in &object_names {
            assert!(listed_objects.contains(&name.to_string()));
        }
        Ok(())
    }
}
