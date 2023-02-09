# tinymap

[![Build Status](https://dev.azure.com/jtnunley01/gui-tools/_apis/build/status/not-a-seagull.tinymap?branchName=master)](https://dev.azure.com/jtnunley01/gui-tools/_build/latest?definitionId=9&branchName=master)
[![crates.io](https://img.shields.io/crates/v/tinymap)](https://crates.io/crates/tinymap)
[![docs.rs](https://docs.rs/tinymap/badge.svg)](https://docs.rs/tinymap)

An implementation of a binary tree-based map that uses the `ArrayVec` from the `tinyvec` crate as its backing. This should not be used outside of projects that require `#![no_std]`. Even if your project is using `#![no_std]`, consider having a feature gate that allows the usage of `HashMap` or a similar type if the `alloc` crate is available. The main purpose of this crate is to provide a similar API to `HashMap` as a last resort in the event that `HashMap` is not available.

This project, similarly to `tinyvec`, also does not use any unsafe code.

# License

This crate is dual-licensed under the Apache 2.0 License and the MIT license. Either can be used at your option.
