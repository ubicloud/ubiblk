use super::ArchiveStore;
use crate::Result;
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

    fn validate_path(&self, path: &PathBuf) -> Result<()> {
        if path.file_name().is_none()
            || path.file_name() == Some(std::ffi::OsStr::new("."))
            || path.file_name() == Some(std::ffi::OsStr::new(".."))
            || path.parent() != Some(&self.base_path)
        {
            return Err(crate::UbiblkError::ArchiveError {
                description: format!(
                    "Invalid object name resulting in path not directly under base directory: {:?}",
                    path
                ),
            });
        }
        Ok(())
    }

    fn try_put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        let mut path = self.base_path.clone();
        path.push(name);
        self.validate_path(&path)?;
        fs::write(path, data)?;
        Ok(())
    }

    fn try_get_object(&self, name: &str) -> Result<Vec<u8>> {
        let mut path = self.base_path.clone();
        path.push(name);
        self.validate_path(&path)?;
        let data = fs::read(path)?;
        Ok(data)
    }
}

impl ArchiveStore for FileSystemStore {
    fn start_put_object(&mut self, name: &str, data: &[u8]) {
        let result = self.try_put_object(name, data);
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

    fn list_objects(&self) -> Result<Vec<String>> {
        let mut objects = Vec::new();
        for entry in fs::read_dir(&self.base_path)? {
            let entry = entry?;
            if !entry.file_type()?.is_file() {
                continue;
            }

            match entry.file_name().to_str() {
                Some(name) => objects.push(name.to_string()),
                None => {
                    return Err(crate::UbiblkError::ArchiveError {
                        description: format!("Invalid UTF-8 in file name: {:?}", entry.file_name()),
                    });
                }
            }
        }
        Ok(objects)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::ffi::OsStringExt;
    use tempfile::tempdir;

    #[test]
    fn test_filesystem_put_and_get() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;
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
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;
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

    #[test]
    fn test_invalid_utf8_file_name() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let store = FileSystemStore::new(dir.path().to_path_buf())?;

        let invalid_name = std::ffi::OsString::from_vec(vec![0xff, 0xfe, 0xfd]);

        let path = dir.path().join(&invalid_name);
        fs::write(&path, b"data")?;

        let err = store.list_objects().unwrap_err();
        assert!(err.to_string().contains("Invalid UTF-8"));

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

    #[test]
    fn test_path_escape_attempt() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;

        let invalid_name = "../outside_object";

        let err = store.put_object(invalid_name, b"data").unwrap_err();
        assert!(err.to_string().contains("Invalid object name"));

        Ok(())
    }

    #[test]
    fn test_errors_on_subdirectory() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;

        let object_name = "subdir/object";

        let err = store.put_object(object_name, b"data").unwrap_err();
        assert!(err.to_string().contains("Invalid object name"));

        Ok(())
    }

    #[test]
    fn test_rejects_cur_dir() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;

        let object_name = ".";

        let err = store.put_object(object_name, b"data").unwrap_err();
        assert!(err.to_string().contains("Invalid object name"));

        Ok(())
    }

    #[test]
    fn test_rejects_parent_dir() -> Result<()> {
        let dir = tempdir()?;
        let mut store = FileSystemStore::new(dir.path().to_path_buf())?;

        let object_name = "..";

        let err = store.put_object(object_name, b"data").unwrap_err();
        assert!(err.to_string().contains("Invalid object name"));

        Ok(())
    }
}
