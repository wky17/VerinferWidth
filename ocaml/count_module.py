#!/usr/bin/env python3
import sys
import re
from collections import defaultdict

def process_file(file_obj):
    module_names = []          # 按出现顺序保存所有 module 名字
    inst_counter = defaultdict(int)   # 统计 inst aof 中引用的模块名次数

    # 正则表达式
    module_pattern = re.compile(r'^module\s+(\S+)\s*:')
    inst_pattern = re.compile(r'^inst\s+\S+\s+aof\s+(\S+)')

    for line in file_obj:
        line = line.strip()
        if not line:
            continue

        # 匹配 module 行
        m = module_pattern.match(line)
        if m:
            name = m.group(1)
            module_names.append(name)
            continue

        # 匹配 inst 行
        m = inst_pattern.match(line)
        if m:
            ref_name = m.group(1)
            inst_counter[ref_name] += 1
            # 注意：不要求该 ref_name 必须在 module_names 中出现过，直接统计

    # 输出结果
    print("=== 记录到的模块定义（按出现顺序）===")
    for name in module_names:
        print(f"  {name}")

    print("\n=== inst aof 语句中引用的模块名及出现次数 ===")
    if not inst_counter:
        print("  无")
    else:
        for name, count in sorted(inst_counter.items()):
            print(f"  {name}: {count}")

def main():
    if len(sys.argv) > 1:
        filename = sys.argv[1]
        try:
            with open(filename, 'r', encoding='utf-8') as f:
                process_file(f)
        except FileNotFoundError:
            print(f"错误：文件 '{filename}' 不存在", file=sys.stderr)
            sys.exit(1)
    else:
        # 从标准输入读取
        process_file(sys.stdin)

if __name__ == "__main__":
    main()