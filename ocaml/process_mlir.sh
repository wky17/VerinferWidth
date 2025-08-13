#!/bin/bash

# 检查是否提供了文件名参数
if [ $# -ne 1 ]; then
    echo "Usage: $0 <mlir_file>"
    exit 1
fi

MLIR_FILE="$1"

# 检查文件是否存在
if [[ ! -f "$MLIR_FILE" ]]; then
    echo "Error: File $MLIR_FILE not found."
    exit 1
fi

# 检查文件扩展名
if [[ "$MLIR_FILE" != *.mlir ]]; then
    echo "Error: $MLIR_FILE is not an .mlir file"
    exit 1
fi

# 创建临时文件
tmp_file=$(mktemp) || { echo "Failed to create temp file"; exit 1; }

# 提取所需内容到临时文件
grep -E \
-e 'firrtl\.circuit' \
-e '^[[:space:]]*firrtl\.module' \
-e 'firrtl\.reg %' \
-e 'firrtl\.regreset %' \
-e 'firrtl\.instance' \
-e '^[[:space:]]*%[^=]*[[:alpha:]_][^=]*=.*firrtl\.node' \
-e '^[[:space:]]*%[^=]*[[:alpha:]_][^=]*=.*firrtl\.wire' \
"$MLIR_FILE" > "$tmp_file"

# 用临时文件替换原文件
mv "$tmp_file" "$MLIR_FILE"
echo "Processed: $MLIR_FILE"