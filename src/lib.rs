#![no_std]

extern crate alloc;
extern crate hashbrown;

#[cfg(not(feature = "compact_str"))]
pub(crate) type String = alloc::string::String;
#[cfg(feature = "compact_str")]
pub(crate) type String = compact_str::CompactString;

#[allow(clippy::match_like_matches_macro)]
mod lexer;
pub mod pp;
pub mod token;

#[cfg(test)]
mod lexer_tests;
#[cfg(test)]
mod pp_tests;
