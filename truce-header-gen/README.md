# truce-header-gen

Command line utility that accepts an event id mapping file
and a tracer id mapping file and generates C code containing
convenience definitions of those ids.

## Example

Given an event id mapping file like:

```csv
id,name,description
90,purchase,whenever someone purchases something in the system
```

and a tracer id mapping file like:

```csv
id,name,description
314,purchase,whenever someone purchases something in the system
271,purchase,whenever someone purchases something in the system
```
