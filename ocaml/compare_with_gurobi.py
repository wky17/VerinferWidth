#!/usr/bin/env python
# coding: utf-8

# In[1]:


import gurobipy as gp
from gurobipy import GRB
import re
import time

# In[14]:


def read_file_to_list(file_path):

    with open(file_path, 'r', encoding='utf-8') as file:
        lines = file.read().splitlines()
    return lines


def replace_suffix_regex(input_str: str) -> str:
    """使用正则表达式实现的版本（推荐）"""
    return re.sub(r'_cons\.txt$', '_res_num.txt', input_str)
        

def check_solution(model, filepath):
    # 读取用户保存的结果文件
    user_results = {}
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                # 分割变量名和值
                parts = line.split(':')
                if len(parts) != 2:
                    print(f"忽略格式错误的行: {line}")
                    continue
                var_name = parts[0].strip()
                value = float(parts[1].strip())
                user_results[var_name] = value
    except FileNotFoundError:
        print(f"错误：文件 '{filepath}' 未找到。")
        return
    except Exception as e:
        print(f"读取文件时出错: {e}")
        return

    # 获取Gurobi的解
    gurobi_results = {v.varName: v.x for v in model.getVars()}

    # 比较结果
    all_matched = True
    for var_name, user_val in user_results.items():
        if var_name not in gurobi_results:
            print(f"警告：变量 '{var_name}' 存在于文件中但未在模型中找到。")
            all_matched = False
            continue
        grb_val = gurobi_results[var_name]
        # 考虑浮点精度误差（1e-6为容忍度）
        if not abs(user_val - grb_val) <= 1e-6:
            print(f"不一致：'{var_name}' 文件值={user_val}, Gurobi值={grb_val}")
            all_matched = False
        else:
            print(f"value equal for '{var_name}' = {user_val}")

    # 输出总结
    if all_matched:
        print("\nThe values of all variables match!")
    else:
        print("\n存在不一致的值。")


def solve_by_gurobi(file_path):
    string_list = read_file_to_list(file_path)

    start = time.time()
    # 创建模型
    model = gp.Model("linear_constraints")
    model.Params.Threads = 1

    # 用于存储变量的字典
    variables = {}

    # 正则表达式用于解析约束
    pattern = re.compile(r'x\((\d+),(\d+)\)')

    # 添加变量（整数类型，且非负）
    for constraint in string_list:
        matches = pattern.findall(constraint)
        for match in matches:
            var_name = f"x({match[0]},{match[1]})"
            if var_name not in variables:
                variables[var_name] = model.addVar(vtype=GRB.INTEGER, lb=0, name=var_name)

    # 更新模型以添加变量
    model.update()

    # 添加约束
    for constraint in string_list:
        constraint = constraint.strip()
        if not constraint:
            continue
        
        # 新增分支：处理 x(...) = min(x(...),x(...)) 格式
        if '= min(' in constraint:
            # 使用正则精准匹配min表达式
            min_match = re.match(r'^(\w+\(\d+,\d+\))\s*=\s*min\((\w+\(\d+,\d+\))\s*,\s*(\w+\(\d+,\d+\))\)$', constraint)
            if min_match:
                lhs_var_name = min_match.group(1).strip()
                var1_name = min_match.group(2).strip()
                var2_name = min_match.group(3).strip()
                
                # 获取变量对象
                lhs_var = variables[lhs_var_name]
                var1 = variables[var1_name]
                var2 = variables[var2_name]
                
                # 添加Gurobi通用约束
                model.addGenConstrMin(lhs_var, [var1, var2], name=f"min_{lhs_var_name}")
                continue  # 处理完成后跳过后续逻辑
        
        # 分离左右部分
        lhs, rhs = constraint.split('>=')
        lhs_str = lhs.strip()
        rhs = rhs.strip()
        
        # 解析右侧表达式
        rhs_terms = rhs.split('+')
        expr = gp.LinExpr()
        for term in rhs_terms:
            term = term.strip()
            if not term:
                continue  # 跳过空字符串
            if 'x' in term:
                # 处理变量项，可能包含负系数
                coeff_part, var_part = term.split('*')
                coeff = int(coeff_part.strip())
                var_name = var_part.strip()
                var = variables[var_name]
                expr += coeff * var
            else:
                # 处理常数项
                const = int(term.strip())
                expr += const
        
        # 处理左侧并添加约束
        if lhs_str in variables:
            # 第一种形式：变量 >= 表达式
            lhs_var = variables[lhs_str]
            model.addConstr(lhs_var >= expr, name=f"constr_var_{lhs_str}")
        else:
            # 第二种形式：表达式 <= 常数
            cst_left = int(lhs_str)
            model.addConstr(expr <= cst_left, name=f"constr_cst_{cst_left}")
        
    # 设置目标函数：最小化所有变量之和
    obj = gp.quicksum(variables.values())
    model.setObjective(obj, GRB.MINIMIZE)

    # 求解模型
    model.optimize()
    end = time.time()

    # 输出结果
    if model.status == GRB.OPTIMAL:
        #print(f"Total cost : {model.objVal}")
        print(f"time cost : {end - start:.6f}s")
    else:
        print("No optimal solution found.")
        
    res_filepath = replace_suffix_regex(file_path)
    check_solution(model, res_filepath)


import sys


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <input_file>")
        sys.exit(1)
    
    file_path = sys.argv[1]  # 获取命令行参数
    solve_by_gurobi(file_path)
