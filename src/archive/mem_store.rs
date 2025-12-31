use std::collections::HashMap;

use super::*;

pub struct MemStore {
    objects: HashMap<String, Vec<u8>>,
}

impl MemStore {
    pub fn new() -> Self {
        MemStore {
            objects: HashMap::new(),
        }
    }
}

impl ArchiveStore for MemStore {
    fn put_object(&mut self, name: &str, data: &[u8]) -> Result<()> {
        self.objects.insert(name.to_string(), data.to_vec());
        Ok(())
    }

    fn get_object(&self, name: &str) -> Result<Vec<u8>> {
        match self.objects.get(name) {
            Some(data) => Ok(data.clone()),
            None => Err(crate::UbiblkError::ArchiveError {
                description: format!("Object {} not found", name),
            }),
        }
    }

    fn list_objects(&self) -> Result<Vec<String>> {
        Ok(self.objects.keys().cloned().collect())
    }
}
