#![warn(missing_docs)]
#![warn(invalid_doc_attributes)]
#![warn(clippy::doc_markdown)]

//! arena allocators

mod simple;

pub use simple::*;

// epoch based allocator that allows arbitrary numbers of weak references

