# ekotrace-cli

`ekotrace` command line utility.

## Getting Started

```bash
cargo install --git ssh://git@github.com/auxoncorp/ekotrace ekotrace-cli --bin ekotrace --force
```

## Usage

The `ekotrace` tracing system relies on two sets of globally unique IDs: tracer
location ids and event ids. While the system can work with nothing but numbers,
we provide a way to define named tracers and events via CSV files. This allows
managing these files as spreadsheets, which is handy because the events file in
particular may become quite large.

### Id Management Format

Ids and metadata for tracer locations or events can be defined in a
CSV file. The columns are `id`, `name`, and `description`.

Tracer location ids and event ids should be defined in separate files.

+ **id**: Positive integer id
  + Unique within the system under test
  + Unique within each file
  + Tracer location ids must be greater than 0 and less than 2147483647.
  + Event ids must be greater than 0 and less than 2147483391.
+ **name**: Single ASCII word identifier for the item
  + Unique within the system under test
  + Unique within each file
+ **description**: Human-oriented ASCII string metadata,
typically elaborating on purpose or intent for future users

#### manifest-gen

Generates event and tracer id manifest files from ekotrace event recording
invocations in source code.

##### Example

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

#### header-gen

Accepts an event id mapping file and a tracer location id mapping file,
generates C or Rust code containing convenience definitions of those ids.

##### Example

Given a tracer id mapping file like:

```csv
id,name,description
271,server_foo,our backend server
314,credit_card_scanner_a,main scanner device
315,credit_card_scanner_b,backup failover scanner
```

and an event id mapping file like:

```csv
id,name,description
90,purchase,whenever someone purchases something in the system
92,unauth_access_error,someone with incorrect permissions tried to use the system
```

The generated C file will contain content similar to:

```c
#define SERVER_FOO 271
#define CREDIT_CARD_SCANNER_A 314
#define CREDIT_CARD_SCANNER_B 315

#define PURCHASE 90
#define UNAUTH_ACCESS_ERROR 92
```

Then, in a project that includes the generated file, one can refer to the
named tracer locations and events without paying attention in the code
to the exact numeric value of the ids.


```c
#include "ekotrace.h"
#include "generated_ekotrace_ids.h"

int main() {
    uint8_t * storage = (uint8_t*)malloc(512);
    ekotrace * t;
    ekotrace_result result = ekotrace_initialize(storage, 512, SERVER, &t);
    if (result != EKOTRACE_RESULT_OK) {
        return 1;
    }
    result = ekotrace_record_event(t, PURCHASE);
    if (result != EKOTRACE_RESULT_OK) {
        return 1;
    }
    return 0;
}
```

#### analysis

Provides several examples of analysis that can be done with such trace data.

## License

Please see [LICENSE](../LICENSE) for more details.
