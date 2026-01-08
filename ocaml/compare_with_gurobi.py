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
        else:
            print(f"value equal for '{var_name}' = {user_val}")

    if all_matched:
        print("\nThe values of all variables match!")
    else:
        print("\nThere are inconsistent values.")


def solve_by_gurobi(file_path):
    string_list = read_file_to_list(file_path)

    start = time.time()
    model = gp.Model("linear_constraints")
    model.Params.Threads = 1

    variables = {}

    pattern = re.compile(r'x\((\d+),(\d+)\)')

    for constraint in string_list:
        matches = pattern.findall(constraint)
        for match in matches:
            var_name = f"x({match[0]},{match[1]})"
            if var_name not in variables:
                variables[var_name] = model.addVar(vtype=GRB.INTEGER, lb=0, name=var_name)

    model.update()

    for constraint in string_list:
        constraint = constraint.strip()
        if not constraint:
            continue
        
        if '= min(' in constraint:
            min_match = re.match(r'^(\w+\(\d+,\d+\))\s*=\s*min\((\w+\(\d+,\d+\))\s*,\s*(\w+\(\d+,\d+\))\)$', constraint)
            if min_match:
                lhs_var_name = min_match.group(1).strip()
                var1_name = min_match.group(2).strip()
                var2_name = min_match.group(3).strip()
                
                lhs_var = variables[lhs_var_name]
                var1 = variables[var1_name]
                var2 = variables[var2_name]
                
                model.addGenConstrMin(lhs_var, [var1, var2], name=f"min_{lhs_var_name}")
                continue 
        
        lhs, rhs = constraint.split('>=')
        lhs_str = lhs.strip()
        rhs = rhs.strip()
        
        rhs_terms = rhs.split('+')
        expr = gp.LinExpr()
        for term in rhs_terms:
            term = term.strip()
            if not term:
                continue  
            if 'x' in term:
                coeff_part, var_part = term.split('*')
                coeff = int(coeff_part.strip())
                var_name = var_part.strip()
                var = variables[var_name]
                expr += coeff * var
            else:
                const = int(term.strip())
                expr += const
        
        if lhs_str in variables:
            lhs_var = variables[lhs_str]
            model.addConstr(lhs_var >= expr, name=f"constr_var_{lhs_str}")
        else:
            cst_left = int(lhs_str)
            model.addConstr(expr <= cst_left, name=f"constr_cst_{cst_left}")
        
    obj = gp.quicksum(variables.values())
    model.setObjective(obj, GRB.MINIMIZE)

    model.optimize()
    end = time.time()

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
    
    file_path = sys.argv[1] 
    solve_by_gurobi(file_path)
