#!/bin/bash
#
# This script is intended to be ran from the Makefile test target

set -e

CLI="../../target/debug/modality-probe"
COLLECTOR="../../target/debug/modality-probe-udp-collector"
APP="./c-example"
ARTIFACTS_DIR="artifacts/"
REPORT_LOG="$ARTIFACTS_DIR/report_log"
GRAPH_DOT="$ARTIFACTS_DIR/graph.dot"

mkdir -p "$ARTIFACTS_DIR"
rm -f "$ARTIFACTS_DIR/*"

if [ ! -f "$APP" ] || [ ! -f "$CLI" ] || [ ! -f "$COLLECTOR" ]; then
    echo "Run this script from the Makefile test target: make test"
    exit 1
fi

# Start up the UDP collector
"$COLLECTOR" --port 2718 --session-id 1 --output-file "$REPORT_LOG" &
COLLECTOR_PID=$!
echo "Started the UDP collector, process-id: $COLLECTOR_PID"
sleep 1

# Start up the example application
"$APP" &
APP_PID=$!
echo "Started the example application, process-id: $APP_PID"

# Run the example for a few seconds
sleep 5

# Gracefully terminate the application
kill -SIGINT $APP_PID
wait $APP_PID

# Gracefully terminate the UDP collector
kill -SIGINT $COLLECTOR_PID
wait $COLLECTOR_PID

# Use the cli to export a graph
"$CLI" export cyclic --components example-component --report "$REPORT_LOG" > "$GRAPH_DOT"

exit 0
