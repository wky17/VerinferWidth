#!/usr/bin/env python
# coding: utf-8

import gurobipy as gp
from gurobipy import GRB
import re
import time

def read_file_to_list(file_path):
    with open(file_path, 'r', encoding='utf-8') as file:
        lines = file.read().splitlines()
    return lines

def replace_suffix_regex(input_str: str) -> str:
    return re.sub(r'_cons\.txt$', '_res_num.txt', input_str)

def check_solution(model, filepath):
    user_results = {}
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                parts = line.split(':')
                if len(parts) != 2:
                    print(f"Ignore the lines with formatting errors : {line}")
                    continue
                var_name = parts[0].strip()
                value = float(parts[1].strip())
                user_results[var_name] = value
    except FileNotFoundError:
        print(f"error : file '{filepath}' not found")
        return
    except Exception as e:
        print(f"Error occurred while reading the file : {e}")
        return

    gurobi_results = {v.varName: v.x for v in model.getVars()}

    all_matched = True
    for var_name, user_val in user_results.items():
        if var_name not in gurobi_results:
            print(f"warning : Variable '{var_name}' exists in our result but not found in the Gurobi model.")
            all_matched = False
            continue
        grb_val = gurobi_results[var_name]
        if not abs(user_val - grb_val) <= 1e-6:
            print(f"not match : '{var_name}' our value = {user_val}, Gurobi value = {grb_val}")
            all_matched = False
        #else:
        #    print(f"value equal for '{var_name}' = {user_val}")

    if all_matched:
        print("\nThe values of all variables match!")
    else:
        print("\nThere are inconsistent values.")

def solve_by_gurobi(file_path):
    string_list = read_file_to_list(file_path)

    start = time.time()
    model = gp.Model("nonlinear_constraints")
    model.params.NonConvex = 2
    model.Params.Threads = 8

    variables = {}
    exp_aux_vars = {}

    # 新的正则：匹配 x(数字,(数字,数字)) 格式
    var_pattern = re.compile(r'x\((\d+),\((\d+),(\d+)\)\)')
    # 辅助函数：从匹配结果生成变量名字符串
    def make_var_name(i, j, k):
        return f"x({i},({j},{k}))"

    # 第一次遍历：收集所有出现的变量名
    for constraint in string_list:
        matches = var_pattern.findall(constraint)
        for match in matches:
            i, j, k = match
            var_name = make_var_name(i, j, k)
            if var_name not in variables:
                variables[var_name] = model.addVar(vtype=GRB.INTEGER, lb=0, name=var_name)

    model.update()

    # 获取或创建指数辅助变量
    def get_exp_aux(base, exp_var):
        key = (base, exp_var.varName)
        if key in exp_aux_vars:
            return exp_aux_vars[key]
        aux_name = f"exp_aux_{base}_{exp_var.varName}"
        aux = model.addVar(vtype=GRB.CONTINUOUS, lb=0, name=aux_name)
        model.addGenConstrExpA(exp_var, aux, float(base), name=f"exp_{base}_{exp_var.varName}")
        exp_aux_vars[key] = aux
        return aux

    # 指数项正则：匹配 底数 ^ x(数字,(数字,数字))
    exp_pattern = re.compile(r'^(\d+)\s*\^\s*x\((\d+),\((\d+),(\d+)\)\)$')

    for constraint in string_list:
        constraint = constraint.strip()
        if not constraint:
            continue

        # 处理 min 约束（注意变量名格式也要匹配新格式）
        if '= min(' in constraint:
            # 匹配形如 x(...,(...)) = min( x(...,(...)) , x(...,(...)) )
            min_match = re.match(r'^(x\(\d+,\(\d+,\d+\)\))\s*=\s*min\((x\(\d+,\(\d+,\d+\)\))\s*,\s*(x\(\d+,\(\d+,\d+\)\))\)$', constraint)
            if min_match:
                lhs_var_name = min_match.group(1)
                var1_name = min_match.group(2)
                var2_name = min_match.group(3)
                lhs_var = variables.get(lhs_var_name)
                var1 = variables.get(var1_name)
                var2 = variables.get(var2_name)
                if lhs_var is None or var1 is None or var2 is None:
                    # 理论上都应该存在，但若缺失则创建
                    if lhs_var is None:
                        lhs_var = model.addVar(vtype=GRB.INTEGER, lb=0, name=lhs_var_name)
                        variables[lhs_var_name] = lhs_var
                    if var1 is None:
                        var1 = model.addVar(vtype=GRB.INTEGER, lb=0, name=var1_name)
                        variables[var1_name] = var1
                    if var2 is None:
                        var2 = model.addVar(vtype=GRB.INTEGER, lb=0, name=var2_name)
                        variables[var2_name] = var2
                model.addGenConstrMin(lhs_var, [var1, var2], name=f"min_{lhs_var_name}")
                continue

        # 处理普通不等式：lhs >= rhs
        if '>=' not in constraint:
            print(f"跳过无法解析的行: {constraint}")
            continue
        lhs, rhs = constraint.split('>=')
        lhs_str = lhs.strip()
        rhs = rhs.strip()

        # 按 '+' 拆分右侧各项
        rhs_terms = rhs.split('+')
        expr = gp.LinExpr()

        for term in rhs_terms:
            term = term.strip()
            if not term:
                continue

            # 检查是否指数项
            exp_match = exp_pattern.match(term)
            if exp_match:
                base = int(exp_match.group(1))
                var_name = make_var_name(exp_match.group(2), exp_match.group(3), exp_match.group(4))
                exp_var = variables.get(var_name)
                if exp_var is None:
                    exp_var = model.addVar(vtype=GRB.INTEGER, lb=0, name=var_name)
                    variables[var_name] = exp_var
                aux = get_exp_aux(base, exp_var)
                expr += aux
                continue

            # 检查是否线性项：形式如 coeff * x(...) 或者 单独的 x(...)
            if 'x' in term:
                if '*' in term:
                    coeff_part, var_part = term.split('*')
                    coeff = int(coeff_part.strip())
                    var_name = var_part.strip()
                else:
                    coeff = 1
                    var_name = term.strip()
                var = variables.get(var_name)
                if var is None:
                    var = model.addVar(vtype=GRB.INTEGER, lb=0, name=var_name)
                    variables[var_name] = var
                expr += coeff * var
            else:
                # 常数项
                const = int(term)
                expr += const

        # 处理左侧：可以是变量或常数
        if lhs_str in variables:
            lhs_var = variables[lhs_str]
            model.addConstr(lhs_var >= expr, name=f"constr_var_{lhs_str}")
        else:
            # 尝试将左侧转为常数（整数）
            try:
                cst_left = int(lhs_str)
                model.addConstr(expr <= cst_left, name=f"constr_cst_{cst_left}")
            except ValueError:
                print(f"无法识别的左侧表达式: {lhs_str}，跳过该约束")
                continue

    # 目标：最小化所有原始变量之和（不包括辅助变量）
    obj = gp.quicksum(variables.values())
    model.setObjective(obj, GRB.MINIMIZE)

    model.optimize()
    end = time.time()

    if model.status == GRB.OPTIMAL:
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

    file_path = sys.argv[1]
    solve_by_gurobi(file_path)