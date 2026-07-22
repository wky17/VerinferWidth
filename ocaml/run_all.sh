#!/bin/bash

# 定义输出文件（若需要绝对路径可修改）
OUTPUT_FILE="output.txt"

# 清空或创建输出文件
> "$OUTPUT_FILE"

# 目标目录（注意路径中的空格用引号包裹）
TARGET_DIR="./demo/firrtl program/"

# 遍历所有 .fir 文件
for file in "$TARGET_DIR"*.fir; do
    # 如果通配符没有匹配到任何文件，$file 就是字面量 "*.fir"
    if [ -f "$file" ]; then
        echo "====== 处理文件: $file ======" >> "$OUTPUT_FILE"
        python count_module.py "$file" >> "$OUTPUT_FILE" 2>&1
        echo "" >> "$OUTPUT_FILE"
    fi
done

echo "所有文件处理完毕，结果保存在 $OUTPUT_FILE"