# modality-probe-capi-impl

This crate is a Rust library containing C-friendly adapters of the
essential [modality-probe](../../../) functions.

The [modality-probe-capi](../../) project is the primary user of this
library. These two projects are separated in order to allow alternate
implementations of the panic-handling apparatus required by Rust
libraries built for C.

If you're looking to get started with using `modality-probe` from C,
you should probably be using [modality-probe](../../) instead.
