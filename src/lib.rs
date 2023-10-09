// #![warn(missing_docs)]
#![warn(invalid_doc_attributes)]
#![warn(clippy::doc_markdown)]

//! arena allocators

pub mod simple;
pub mod sync;

// pub use simple::*;

// epoch based allocator that allows arbitrary numbers of weak references
