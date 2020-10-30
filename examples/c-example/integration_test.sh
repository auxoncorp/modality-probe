#!/bin/bash
#
# This script is intended to be ran from the Makefile test target

set -e

CLI="../../target/debug/modality-probe"
COLLECTOR="../../target/debug/modality-probe-udp-collector"
APP="./c-example"
ARTIFACTS_DIR="artifacts"
REPORT_LOG="$ARTIFACTS_DIR/report_log.jsonl"
CYCLIC_GRAPH_DOT="$ARTIFACTS_DIR/cyclic_graph.dot"
ACYCLIC_GRAPH_DOT="$ARTIFACTS_DIR/acyclic_graph.dot"

if [ ! -f "$APP" ] || [ ! -f "$CLI" ] || [ ! -f "$COLLECTOR" ]; then
    echo "Run this script from the Makefile test target: make test"
    exit 1
fi

mkdir -p "$ARTIFACTS_DIR"
rm -f "$ARTIFACTS_DIR/"*

# Start up the UDP collector
"$COLLECTOR" --port 2718 --session-id 1 --output-file "$REPORT_LOG" &
COLLECTOR_PID=$!
echo "Started the UDP collector, process-id: $COLLECTOR_PID"
sleep 1

# Run the example application
"$APP"

# Gracefully terminate the UDP collector
sleep 1
kill -SIGINT $COLLECTOR_PID
wait $COLLECTOR_PID

# Use the cli to export a dot graph
"$CLI" visualize cyclic --component-path example-component --report "$REPORT_LOG" > "$CYCLIC_GRAPH_DOT"
"$CLI" visualize acyclic --component-path example-component --report "$REPORT_LOG" > "$ACYCLIC_GRAPH_DOT"

if [ ! -s "$CYCLIC_GRAPH_DOT" ]; then
    echo "$CYCLIC_GRAPH_DOT is empty"
    exit 1
fi

if [ ! -s "$ACYCLIC_GRAPH_DOT" ]; then
    echo "$ACYCLIC_GRAPH_DOT is empty"
    exit 1
fi

exit 0
