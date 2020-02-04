# ekotrace-manifest-gen

Command line utility that generates event and tracer id manifest files from
ekotrace event recording invocations in source code.

## Example

Given some C/C++ source file with ekotrace event recording invocations like:

```c
ekotrace_initialize(storage_bytes, TRACER_SIZE, LOCATION_ID_FOO, &ekotrace_instance);

ekotrace_record_event(ekotrace_instance, EVENT_A);
```

or in Rust, invocations like:

```rust
let ekotrace_instance = Ekotrace::try_initialize_at(&mut storage_bytes, LOCATION_ID_FOO)?;

ekotrace_instance.record_event(EVENT_A);
```

The generated manifest files will contain:

```csv
# tracers.csv
id,name,description
1,location_id_foo,
```

```csv
# events.csv
id,name,description
1,event_a,
```
