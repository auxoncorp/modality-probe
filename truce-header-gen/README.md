# truce-header-gen

Command line utility that accepts an event id mapping file
and a tracer id mapping file and generates C code containing
convenience definitions of those ids.

## Example

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
#define TR_SERVER_FOO 271
#define TR_CREDIT_CARD_SCANNER_A 314
#define TR_CREDIT_CARD_SCANNER_B 315

#define EV_PURCHASE 90
#define EV_UNAUTH_ACCESS_ERROR 92
```
