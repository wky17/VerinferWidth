#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Usage: $0 <mlir_file>"
    exit 1
fi

MLIR_FILE="$1"

if [[ ! -f "$MLIR_FILE" ]]; then
    echo "Error: File $MLIR_FILE not found."
    exit 1
fi

if [[ "$MLIR_FILE" != *.mlir ]]; then
    echo "Error: $MLIR_FILE is not an .mlir file"
    exit 1
fi

tmp_file=$(mktemp) || { echo "Failed to create temp file"; exit 1; }

grep -E \
-e 'firrtl\.circuit' \
-e '^[[:space:]]*firrtl\.module' \
-e 'firrtl\.reg %' \
-e 'firrtl\.regreset %' \
-e 'firrtl\.instance' \
-e '^[[:space:]]*%[^=]*[[:alpha:]_][^=]*=.*firrtl\.node' \
-e '^[[:space:]]*%[^=]*[[:alpha:]_][^=]*=.*firrtl\.wire' \
"$MLIR_FILE" > "$tmp_file"

mv "$tmp_file" "$MLIR_FILE"
echo "Processed: $MLIR_FILE"