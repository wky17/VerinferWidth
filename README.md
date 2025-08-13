# VerinferWidth
## Abstract
FIRRTL is an intermediate representation language for Register Transfer Level (RTL) hardware designs. In FIRRTL programs, the bit widths of some components may not be given explicitly, thus they must be inferred during compilation. In mainstream FIRRTL compilers such as firtool, the width inference is conducted by a compilation pass called InferWidths, which may fail even for simple FIRRTL programs. In this paper, we investigate the width inference problem for FIRRTL programs. We show that if the constraint obtained from a FIRRTL program is satisfiable, there must exist a unique least solution. Based on this result, we propose a complete procedure for solving the width inference problem, which can handle programs while firtool may fail. We implement the procedure in Rocq and prove its correctness. From the Rocq implementation, we extract an OCaml implementation, which is the first formally verified InferWidths pass. Extensive experiments demonstrate that it can solve more instances than the official InferWidths pass in firtool using less time.

## Installation
To compile the Coq formalization, the following packages are required.

* [Coq](https://coq.inria.fr) 8.16.0 
* [MathComp](https://github.com/math-comp/math-comp) 2.2.0
* [MathComp-tarjan](https://github.com/coq-community/tarjan) 1.0.2
* [Ocaml](https://ocaml.org) 4.14.1 
* [Ocamgraph](https://github.com/backtracking/ocamlgraph/) 2.1.0
* [dune](https://github.com/ocaml/dune) 3.16.0
* [Gurobi](https://www.gurobi.com) 12.0.1
* [circt](https://github.com/llvm/circt/)

## Initialize
```bash
# generate configuration file
coq_makefile -f _CoqProject -o Makefile

# initialize an ocaml project
dune init proj ocaml

# make and the extracted OCaml files are generated in ocaml/extraction
make

# enter the subdirectory
cd ocaml
```

## Run
This tool provides bitwidth inference capabilities for FIRRTL (Flexible Intermediate Representation for RTL) circuits. To test different functionalities, modify the called **function name** in `hipparser.ml` and compile.

**Important Preprocessing Step**:  
FIRRTL uses indentation to determine nested levels of `when...else...` blocks, which complicates parsing. **Always** preprocess FIRRTL files with:
```bash
python transform_when_blocks.py ./your/path/to/example.fir
```

---

### 1. OCaml inferWidths
**Function name**: `Min_solver.print_iw_fir` (set in `hipparser.ml`)  

- **Input**: FIRRTL file (e.g., `example.fir`)  
- **Output**: Circuit with inferred bitwidths (`example_iw.fir`)  

```
# compile the project
dune build

# run the execution file
./_build/default/hipparser.exe ./your/path/to/example.fir

```

The output file `example_iw.fir` can be processed by downstream tools like `firtool`.

---

### 2. Compare with Gurobi
**Function name**: `Against_gurobi.store_cons_res`  (set in `hipparser.ml`)  

- **Input**: FIRRTL file (e.g., `example.fir`)  
- **Outputs**:
  Bitwidth constraints (`example_cons.txt`) and our result (`example_res_num.txt`)

```
# compile the project
dune build

# run the execution file
./_build/default/hipparser.exe ./your/path/to/example.fir
```

To compare with Gurobi:

```bash
python compare_with_gurobi.py example_cons.txt
```

Please place `example_res_num.txt` in the same directory as `example_cons.txt`, it is read automatically.

**Note that** Gurobi only supports basic `a = min(b, c)` expressions (all variables). Manually adjust the constraints if needed.  
**Example Adjustment**:  

- Original: `x(85325,0) >= min(x(85324,0),2)`  
- Modified:
  ```
  x(85324,1) >= 2 # new variable
  x(85325,1) = min(x(85324,0),x(85324,1)) # new variable
  x(85325,0) >= 1 * x(85325,1) + 0
  ```

---

### 3. Compare with firtool

**Prerequisites**:

1. Generate MLIR from [firtool](https://github.com/llvm/circt/releases):
   ```bash
   firtool --mlir-print-ir-after=firrtl-infer-widths ./your/path/to/example.fir &> example.mlir
   ```

2. Ignore connection statements, retain definitions
   ```bash
   ./process_mlir.sh example.mlir
   ```

**Function name**: `Against_firtool.compare_with_mlir` (set in `hipparser.ml`)  

- **Input**: FIRRTL file (e.g., `example.fir`) and inferred MLIR file from firtool (e.g., `example.mlir`)
- **Output**: firtool gives the same result as ours or not?

```
# compile the project
dune build

# run the execution file
./_build/default/hipparser.exe ./your/path/to/example.fir
```
