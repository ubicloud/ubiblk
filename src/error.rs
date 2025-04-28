use std::{error, fmt};

#[derive(Debug)]
pub enum Error {
    ThreadCreation,
    IoChannelCreation,
    GuestMemoryAccess,
    IoError,
    InvalidParameter,
}

pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "vhost_user_block_error: {self:?}")
    }
}

impl error::Error for Error {}
