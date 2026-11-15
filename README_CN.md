# BFWInferWidths

## 安装
编译 Coq 形式化证明需以下依赖包：

* [Coq](https://coq.inria.fr) 8.20
* [MathComp](https://github.com/math-comp/math-comp) 2.2.0
* [MathComp-tarjan](https://github.com/coq-community/tarjan) 1.0.2
* [Ocaml](https://ocaml.org) 4.14.1 
* [Ocamgraph](https://github.com/backtracking/ocamlgraph/) 2.1.0
* [dune](https://github.com/ocaml/dune) 3.16.0
* [Gurobi](https://www.gurobi.com) 12.0.1
* [circt](https://github.com/llvm/circt/)

## 初始化
```bash
# 生成配置文件
coq_makefile -f _CoqProject -o Makefile

# 初始化 OCaml 项目
dune init proj ocaml

# 编译并生成文件到 ocaml/extraction
make

# 进入子目录
cd ocaml
```

隐式位宽语义中的寄存器 reset 值参与位宽迭代：`UInt` / `SInt` 隐式位宽按寄存器当前位宽与 reset 值位宽的较大者更新，显式位宽不变；抽象 Reset 类型使用现有的类型合一规则。reset 控制信号不用于确定寄存器位宽。当前支持 ground 类型及 passive 数组和 bundle；非 passive 类型、类型不匹配或无法确定 reset 值类型时，迭代返回 `None`。该步骤不会反向更新 reset 值来源；reset 控制信号和时钟的合法性不由此步骤检查。

回归测试已列入 `_CoqProject`，也可单独运行：
```bash
opam exec --switch=mathcomp2.0 -- make semantics/Reset_width_tests.vo
```

这些 reset 测试本身不证明一般 FIRRTL 电路的最小不动点与约束求解最小解等价；下述一致性证明仅覆盖共同标量子集。

`semantics/Width_solution_bridge.v` 定义了两种语法共用的单内部模块子集、两边的转换及逐位宽比较接口。该子集仅含标量 `UInt` / `SInt`、时钟输入、wire、reg、skip 和标量连接；表达式仅含引用和显式位宽常量，原始隐式位宽为 0。一致性定理及其证明位于 `semantics/Width_bridge_proofs.v`；使用原定理名的代码需要导入该证明文件。

`semantics/Width_bridge_proofs.v` 给出标量类型映射关系，并证明两端成功构造的单模块初始电路映射满足该关系；证明中考虑了两端端口构造顺序不同。该文件还刻画了共同子集的约束提取，并证明在映射相关、赋值匹配语义映射且每个相关语句的语义操作数有效的条件下，整个提取约束列表的满足性等价于所有对应语义位宽不等式成立。提取按 `expandwhens` 的实际行为处理反转后的语句顺序。此外，已证明成功返回的语义结果是按逐键映射内容比较的不动点。

在共同标量子集内，已进一步证明每个成功的语义迭代步骤保持组件域、kind 和类型类别，显式位宽不变而隐式位宽单调增长；该性质已提升至语句序列、任意次单模块电路迭代以及成功返回的实际语义结果。求解端初始映射与实际语义结果仍满足标量映射关系；引用的源与目标相同时也包含在证明内。表达式类型和数值宽度、以及已经成立的语义操作数有效性均在迭代中保持。

`successful_circuit_initial_operands_ready` 利用求解端初始映射、语义端初始映射和语义迭代成功返回，证明初始映射及结果映射中所有被提取约束涉及的语义操作数均有效；无需额外假设求解器正确性或最小性。零轮迭代也适用，因为语义结果仍须通过额外一轮不动点检查。单独的初始映射成功不足以推出此性质：寄存器声明阶段不会检查 reset 值。`successful_result_extracted_constraints_match_bounds` 据此去除了结果映射相关性与操作数有效性的额外前提，但仍要求提供匹配该映射的赋值。

`successful_circuit_result_stable_width_trace` 证明成功返回的单模块语义结果在额外检查轮次中，每条共同子集语句执行前后的组件映射均逐键相等；`common_stable_width_trace_split` 可按任意语句位置提取实际的前缀、单步和后缀执行及逐键相等性。证明利用宽度增长性，比较的是映射内容而非内部结构；语义迭代使用原始语句顺序，约束提取则使用反转顺序。

进一步地，`stable_connect_semantic_bound` 和 `stable_reg_reset_semantic_bound` 利用单步稳定性证明隐式目标的来源位宽不大于目标位宽，涵盖自引用及 `UInt` / `SInt`；`successful_result_semantic_bounds` 将结果提升到成功语义结果的全部相关语句，覆盖原始与反转顺序。

`semantic_valuation` 从语义组件映射的实际元素构造部分赋值：恰好为每个隐式 `UInt` / `SInt` 的 `(id, 0)` 位置写入当前位宽，不为显式类型、缺失组件或非零偏移添加项。`semantic_result_valuation_satisfies_constraints` 证明该赋值覆盖初始隐式位置并满足全部成功提取的约束，包括没有出现于约束中的隐式位置。

反方向上，`satisfying_valuation_bounds_successful_semantic_result` 证明任意满足全部提取约束、并覆盖初始隐式位置的赋值，都是初始映射、每次成功语句更新和每轮语义迭代的上界，因此也不小于成功返回的不动点。`semantic_result_valuation_le_satisfying_valuation` 以求解器的部分映射序 `constraints.le` 给出该结论；缺失项不视为零。约束满足性本身不保证覆盖无约束的隐式变量，故覆盖前提不可省略。

`extended_semantic_valuation` 以任意基础赋值为起点，用语义结果中的隐式标量位宽覆盖对应的 `(id, 0)` 键，保留其余键的值，因而覆盖基础赋值的定义域；被覆盖的位宽不一定大于基础值。成功的语义结果所构造的扩展赋值覆盖初始隐式位置并满足全部提取约束。

`solver_solution_contract` 明确要求解满足约束，并在满足约束、覆盖初始隐式位置及覆盖该解的定义域的候选赋值中最小。`conditional_single_module_min_solution_matches_fixed_point` 已在这一契约及解覆盖初始隐式位置等前提下闭合：利用扩展赋值和语义迭代上界分别证明两个方向。`conditional_solve_fun_matches_fixed_point` 进一步衔接实际 `solve_fun` 的成功返回，但仍以其提取约束对应的契约和覆盖性为前提。

`successful_single_module_solver_domain` 证明单模块求解成功时，输出赋值的定义域恰为电路的有限类型叶子集合；其中包括无约束的隐式变量和显式类型位置。`successful_solve_fun_covers_initial` 因而从两端初始映射和实际 `solve_fun` 成功推出原始隐式位置的覆盖性。`conditional_solve_fun_matches_fixed_point_without_coverage` 去除了条件版推论中单独的覆盖前提，仍要求求解器契约。

SCC 桥接证明了实际 Kosaraju 列表覆盖有限变量、无重复且每个 SCC 非空；每个分量恰是依赖图中某个代表点的双向可达分量。依赖图的边与约束右侧变量到左侧变量的关系双向对应，包括指数项。`successful_common_solver_extraction_bridge` 证明成功求解时，按 SCC 列表提取的约束与全部扁平约束对于任意赋值具有相同的满足性；并非声称两个列表的顺序相同。

`kosaraju_later_no_edge` 利用 MathComp 反向 DFS 的可达性证明处理顺序中后续分量不会指向当前分量；`solver_sccs_constraint_order` 将此性质通过实际依赖图接到约束变量，无需假设图无环。`successful_common_solver_schedule` 由此证明实际 SCC 调度满足递归求解器所需前提。

普通求解器的递归 SCC 前提已移除不成立的全局 `dominates_at` 条件。成功结果的 `solve_alg_correctness` 进一步改为只要求 `scc_schedule_correctness`（分量非空、无重复、已求解变量不与剩余分量重叠，以及依赖位于当前或已求解分量）和 `extract_entries_correctness`（已存在的约束条目格式正确）；它不再要求每个节点都有非空约束，也不要求替换后的子图强连通。对于共同标量子集，`extracted_common_entries_correct` 证明实际提取满足条目格式，`successful_common_solver_satisfies_if_schedule` 将实际 `solve_fun` 的满足性归约为 SCC 调度条件。

共同标量子集提取的约束均为简单线性形式，且 `remove_solved_simple` 证明代入已求解变量后仍保持该形式；`solve_simple_scc_smallest` 在候选赋值覆盖节点时处理无约束节点，包括单节点空约束。新的 `solve_alg_simple_smallest` 将局部最小性推广到递归结果，无需旧 `solve_alg_smallest` 中的非空提取和强连通前提。`successful_common_solver_contract` 证明实际 `solve_fun` 成功返回的结果满足该子集约束及最小性契约，不再假设 SCC 调度顺序。`solve_fun_matches_fixed_point` 闭合实际求解结果与语义不动点的逐隐式位宽一致性；保留两端类型映射构造、求解及语义迭代成功的前提，不需要另行假设覆盖性或控制信号有效。原陈述 `single_module_min_solution_matches_fixed_point` 也已在证明文件中闭合，保留其原有前提。参考链、环及无约束节点的定理实例以实际求解成功为前提，不声称已计算出完整求解器返回值。

简单环距离矩阵初始化已改为逐条更新递归结果，避免同一左值的约束覆盖彼此。`init_dist_map_weight_spec` 给出任意输入的逐键精确规格：已有行从初始值开始，对空线性项（指向 `Zero`）和单个系数为 1 的线性项逐条取最大值；其他线性项跳过，缺失行不创建。`map0_find_exact` 刻画初始行恰对应节点列表，且仅含零权自环；`init_dist_map_permutation` 证明约束排列不影响任何矩阵项。这一实现与规格均不检查 `rhs_power`，因此不能将其视为支持指数项的 FIRRTL 约束语义。回归测试还检查重复边、负常数、自环、空输入、缺失行和不支持的线性项。

原 Floyd 遍历存在独立缺陷：旧 `inner_loop2` 和 `inner_loop1` 会逐步缩小行和目标节点范围。实际求解器现改用 `floyd_pivots` 和 `floyd_rows`，每个中间节点均遍历完整行集合和完整目标集合；`floyd_loop_map_full_traversal` 精确证明这一遍历结构。旧函数仅为保留原有证明而存在，不再由实际 Floyd 路径调用。原两节点反例在两种节点顺序下均返回满足约束的 `(6, 6)`；回归还检查两节点的有界约束组和三节点正、零、负权环的全部节点排列。

`scc_none_unsat` 证明简单环求解返回 `None` 时不存在满足约束的赋值；`simple_cycle_solution_lower_bound` 证明在无指数项且候选赋值覆盖结果定义域时，成功结果不大于任意满足约束的候选赋值。`floyd_loop_map_contains_constraint` 证明每条受支持约束对应的直接边在完整迭代后仍存在且权重不小于约束常量；`floyd_pivots_via` 证明已存在的两段路径会在其中间节点的遍历步骤中合成。`simple_cycle_satisfies_constant` 无需额外矩阵前提地证明常数约束满足性。

已从成功返回证明节点范围内的路径拼接闭包，并闭合 `simple_cycle_solver_correct` 和 `simple_cycle_solver_none_iff_unsatisfiable`：当约束无指数项、每条线性项为空或仅有一个系数为 1 的变量，且所有约束变量都在节点列表中时，成功结果满足全部约束、定义域恰为节点列表，并且不大于任何覆盖这些节点的满足赋值；返回 `None` 当且仅当不存在满足赋值。候选赋值的覆盖条件对于部分映射是必要的，尤其是节点列表含无约束节点时。节点范围也不可省略：范围外的目标不会被 Floyd 遍历，`floyd_external_destination_requires_scope_premise` 给出了全局闭包不成立的反例。

普通 `inferWidths.v` 面向无指数约束，其简单环判定只检查线性项；指数扩展由 `inferWidths_exp.v` 负责，其判定同时排除指数项。两者在符合各自输入范围时共用修复后的 Floyd 实现和完整简单环契约，且各自的 `solve_scc_correctness` 不再要求 `dominates_at`。上面的全局契约与语义一致性证明适用于普通求解器的共同标量子集，不代表指数扩展或一般 FIRRTL 电路的全局正确性已获证明。

单模块求解器的有限变量集合从电路类型映射中的类型叶子构造，不再要求组件编号小于组件数量。数组元素共享同一组类型叶子；显式类型叶子也包含在有限集合中。依赖约束引用不在集合中的变量时，求解返回 `None`；指数项也参与依赖图的边计算。

## 运行
本工具提供 FIRRTL 电路的位宽推断等功能。通过修改 `hipparser.ml` 中的**函数名**并编译，可测试不同功能。

**关键预处理步骤**：  
FIRRTL 使用缩进确定 `when...else...` 块的嵌套层级，需先执行文本预处理：
```bash
python transform_when_blocks.py ./your/path/to/example.fir
```

---

### 1. OCaml 位宽推断
**函数名**: `Min_solver.print_iw_fir` (在 `hipparser.ml` 中设置)  

- **输入**: FIRRTL 文件 (如 `example.fir`)  
- **输出**: 带位宽推断结果的电路 (`example_iw.fir`)  

```bash
# 编译项目
dune build

# 运行可执行文件
./_build/default/hipparser.exe ./your/path/to/example.fir
```
输出文件 `example_iw.fir` 可被 `firtool` 等FIRRTL工具处理。

---

### 2. 与 Gurobi 对比验证
**函数名**: `Against_gurobi.store_cons_res` (在 `hipparser.ml` 中设置)  

- **输入**: FIRRTL 文件 (如 `example.fir`)  
- **输出**:
  位宽约束 (`example_cons.txt`) 与结果文件 (`example_res_num.txt`)

```bash
# 编译项目
dune build

# 运行可执行文件
./_build/default/hipparser.exe ./your/path/to/example.fir
```

使用 Gurobi 验证结果：
```bash
python compare_with_gurobi.py example_cons.txt
```
请将 `example_res_num.txt` 与 `example_cons.txt` 置于**相同目录**，程序会自动读取。

**注意**：Gurobi 仅支持基础表达式 `a = min(b, c)` (a/b/c 均为变量)。如遇复杂约束需手动调整。  
**调整示例**：

- 原始约束: `x(85325,0) >= min(x(85324,0),2)`  
- 修改后:
  ```text
  x(85324,1) >= 2
  x(85325,1) = min(x(85324,0),x(85324,1))
  x(85325,0) >= 1 * x(85325,1) + 0
  ```

---

### 3. 与 firtool 对比验证

**准备工作**:

1. 使用 [firtool](https://github.com/llvm/circt/releases) 生成 MLIR：
   ```bash
   firtool --mlir-print-ir-after=firrtl-infer-widths ./your/path/to/example.fir &> example.mlir
   ```

2. 过滤元件定义（忽略连接语句）：
   ```bash
   ./process_mlir.sh example.mlir
   ```

**函数名**: `Against_firtool.compare_with_mlir` (在 `hipparser.ml` 中设置)  

- **输入**: FIRRTL 文件 (如 `example.fir`) 和 firtool 生成的 MLIR 文件 (如 `example.mlir`)
- **输出**: firtool 与我们的结果是否一致

```bash
# 编译项目
dune build

# 运行可执行文件
./_build/default/hipparser.exe ./your/path/to/example.fir
```