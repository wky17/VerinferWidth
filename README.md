# VerinferWidth
## Abstract
FIRRTL is an intermediate representation language for Register Transfer Level (RTL) hardware designs. In FIRRTL programs, the bit widths of some components may not be given explicitly, thus they must be inferred during compilation. In mainstream FIRRTL compilers such as firtool, the width inference is conducted by a compilation pass called InferWidths, which may fail even for simple FIRRTL programs. In this paper, we investigate the width inference problem for FIRRTL programs. We show that if the constraint obtained from a FIRRTL program is satisfiable, there must exist a unique least solution. Based on this result, we propose a complete procedure for solving the width inference problem, which can handle programs while firtool may fail. We implement the procedure in Rocq and prove its correctness. From the Rocq implementation, we extract an OCaml implementation, which is the first formally verified InferWidths pass. Extensive experiments demonstrate that it can solve more instances than the official InferWidths pass in firtool using less time.

## Installation
### To compile the Coq formalization, the following packages are required.

* [Coq](https://coq.inria.fr) 8.16.0 
* [MathComp](https://github.com/math-comp/math-comp) 2.2.0
* [MathComp-tarjan](https://github.com/coq-community/tarjan) 1.0.2
* [Ocaml](https://ocaml.org) 4.14.1 
* [Ocamgraph](https://github.com/backtracking/ocamlgraph/) 2.1.0
* [dune](https://github.com/ocaml/dune) 3.16.0

### Run
```bash
# generate configuration file
coq_makefile -f _CoqProject -o Makefile;

# initialize an ocaml project
dune init proj ocaml;

# make and the extracted OCaml files are generated in ocaml/extraction
make;

# enter the subdirectory
cd ocaml;

# compile the project
dune build;

# run the execution file
./_build/default/hipparser.exe ./demo/firrtl_program/example.fir

通过编辑hipparser.ml中所调用的函数名，试用工具的不同功能：
1) 输入hifirrtl例子example.fir，输出经ocaml位宽推断后的电路，保存为example_iw.fir
2) 输入hifirrtl例子example.fir，输出电路中位宽待推断变量对应的约束 和 经ocaml位宽推断算法接出的最小可行解。使用Gurobi的python api来验证解的正确性
3) 输入hifirrtl例子example.fir 和 经firtool inferwidths转换后的mlir中间表示example.mlir。使用ocaml位宽推断算法接出的最小可行解，与firtool输出的结果进行一致性比较
```