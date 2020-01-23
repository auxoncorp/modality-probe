# ekotrace-event-manifest-gen

Command line utility that generates an event id manifest file from
ekotrace event recording invocations in source code.

## Example

Given some C/C++ source file with ekotrace event recording invocations like:

```c
ekotrace_record_event(ekotrace_instance, EVENT_A);
```

or in Rust, invocations like:

```rust
ekotrace_instance.record_event(EVENT_B);
```

The generated event id manifest file will contain:

```csv
id,name,description
1,event_b,
2,event_a,
```
