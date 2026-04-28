#!/bin/bash

# 定义路径
SEARCH_DIR="./demo/firrtl program"
SOLVER="./_build/default/run_solver.exe"
OUTPUT_FILE="output.out"

# 如果输出文件已存在，先清空它
> "$OUTPUT_FILE"

# 检查目录是否存在
if [ ! -d "$SEARCH_DIR" ]; then
    echo "错误: 目录 $SEARCH_DIR 不存在。"
    exit 1
fi

# 遍历目录下的所有 .fir 文件
for fir_file in "$SEARCH_DIR"/*.fir; do
    # 检查是否有匹配的文件（防止目录下没有 .fir 文件时循环报错）
    [ -e "$fir_file" ] || continue

    echo "正在处理: $fir_file ..." | tee -a "$OUTPUT_FILE"
    
    # 运行程序并将标准输出和错误输出都追加到 output.out
    "$SOLVER" "$fir_file" >> "$OUTPUT_FILE" 2>&1
    
    # 在输出文件中添加分隔符，方便阅读
    echo -e "\n------------------------------------------\n" >> "$OUTPUT_FILE"
done

echo "任务完成！所有结果已保存至 $OUTPUT_FILE"
