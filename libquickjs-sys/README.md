# libquickjs-dtp-sys

FFI Bindings for [quickjs](https://bellard.org/quickjs/), a Javascript engine.

This is a fork of the original [libquickjs-sys](https://crates.io/crates/libquickjs-sys)
crate which includes a fully featured date parser, capable of parsing dates like
`Sat, 01-Jan-2000 00:00:00 PST`.

See the [quick-js-dtp](https://crates.io/crates/quick-js-dtp) crate for a high-level
wrapper.


*Version 0.9.0*
**Embedded VERSION: 2021-03-27**

## Embedded vs system

By default, an embedded version of quickjs is used.

If you want to use a version installed on your system, use:


```toml
libquickjs-sys = { version = "...", default-features = false, features = ["system"] }
```


## Updating the embedded bindings

QuickJS sources and a pre-generated `bindings.rs` are included in the repo.

They are used if the `embedded` feature is enabled.

To updat the bindings, follow these steps:

* (Install [just](https://github.com/casey/just))
* Update the download URL in ./justfile
* run `just update-quickjs`
