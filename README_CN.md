# BFWInferWidths

## 安装
编译 Coq 形式化证明需以下依赖包：

* [Coq](https://coq.inria.fr) 8.16.0 
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