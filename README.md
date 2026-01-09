# Artifact for *A Formally Verified Procedure for Width Inference in FIRRTL*

This artifact contains the implementation and formalization accompanying the paper **A Formally Verified Procedure for Width Inference in FIRRTL** by *Wang, Shi, Liu, Wu, Song, Chen, Jansen*. It includes:
- A Coq formalization of **a width inference algorithm and its correctness proofs**
- An OCaml implementation of **a complete procedure for solving the width inference problem in FIRRTL**
- Evaluation datasets and scripts to reproduce the experiments from the paper

## Abstract
FIRRTL is an intermediate representation language for Register Transfer Level (RTL) hardware designs. In FIRRTL programs, the bit widths of some components may not be given explicitly, thus they must be inferred during compilation. In mainstream FIRRTL compilers such as firtool, the width inference is conducted by a compilation pass called InferWidths, which may fail even for simple FIRRTL programs. In this paper, we investigate the width inference problem for FIRRTL programs. We show that if the constraint obtained from a FIRRTL program is satisfiable, there must exist a unique least solution. Based on this result, we propose **a complete procedure** for solving the width inference problem, which can handle programs while firtool may fail. We implement the procedure in Rocq and **prove its correctness**. From the Rocq implementation, we extract **an OCaml implementation**, which is the first formally verified InferWidths pass. Extensive experiments demonstrate that it can solve more instances than the official InferWidths pass in firtool using less time.

## 🚀 Getting Started Guide

### Prerequisites

Choose one of the following two approaches:

#### Option A: Docker (Recommended - 20 minutes)
- Docker Engine 20.10+ 
- 8GB RAM, 5GB disk space

#### Option B: Native Installation
- macOS 12+ or Linux (Ubuntu 22.04+/Debian 11+)
* [OPAM](https://opam.ocaml.org) 2.1+
* [Coq](https://coq.inria.fr) 8.16.0 
* [MathComp](https://github.com/math-comp/math-comp) 2.2.0
* [MathComp-tarjan](https://github.com/coq-community/tarjan) 1.0.2
* [Ocaml](https://ocaml.org) 4.14.1 
* [Ocamgraph](https://github.com/backtracking/ocamlgraph/) 2.1.0
* [dune](https://github.com/ocaml/dune) 3.16.0
* [Gurobi](https://www.gurobi.com) 12.0.1(academic license)
* [firtool](https://github.com/llvm/circt/) latest version

### Installation & Smoke Test

#### Docker Approach:
```bash
# 1. Clone this repository
git clone [GitHub link will be placed here after AE is completed]
chmod -R 777 VerinferWidth/ # Obtain executable permission(not neccessary)
cd Verinferwidth

# 2. Build the Docker image
docker build -t esop-artifact .

# 3. Run the smoke test
docker run --rm esop-artifact ./build_and_run.sh
```

#### Local Approach:
```bash
# 1. Install dependencies (see REQUIREMENTS.txt for detailed versions)
opam pin add coq 8.16.0
opam pin add ocaml 4.14.2
opam install -y \
    coq-mathcomp-algebra=2.2.0 \
    coq-mathcomp-fingroup=2.2.0 \
    coq-mathcomp-ssreflect=2.2.0 \
    coq-mathcomp-tarjan=1.0.2
opam install -y \
    ocamlgraph=2.1.0 
pip install gurobipy

# 2. Run the smoke test
./build_and_run.sh
```

#### Expected Smoke Test Output
```bash
✅ Coq formalization compiled successfully
✅ OCaml implementation built
🚀 Running demo on sample circuit...
extraction time : ...
computation time : ...
total time : ...
components amount : ...
circuit Foo : (the inferred FIRRTL circuit as a result)
  module Foo : 
    input _0 : UInt<1>
    output _1 : UInt<1>
    when _0 : 
      _1 <= UInt<1>(1)
    else : 
      _1 <= UInt<1>(1)
../ocaml/demo/AddNot.fir width inference is finished
🎉 Smoke test completed successfully!
```

### Note
We are using the simple FIRRTL program `AddNot.fir` in `ocaml/demo`, in fact, the benchmarks mentioned in the article are all included in `ocaml/demo/firrtl program`. You can replace the test file path in `build_and_run.sh` with any of the test cases provided by us, for example:
```bash
./_build/default/run_solver.exe ../ocaml/demo/firrtl\ program/GCD.fir
```
Furthermore, we also support any FIRRTL test cases provided by any user. All that is required is a simple preprocessing step (under the `ocaml` directory) :
```bash
python transform_when_blocks.py ./your/path/to/example.fir
```
The preprocessed file will be located in a folder named "preprowhen" under the same directory as the input file.Because FIRRTL uses indentation to determine nested levels of `when...else...` blocks, which complicates parsing. 

In fact, if you run the test locally, you will find a new firrtl file named `AddNot_iw.fir` in the same directory as `AddNot.fir`. This is the new firrtl circuit obtained through our width inference process(it cannot be seen through `docker run`). The output file can be processed by downstream tools like `firtool`.

## 🔬 Reproducing Paper Results

### Part 1: Compare with Gurobi
Before conducting the test, please make sure that you have installed the Gurobi 12.0.1(python API) with an academic license.

Change the file content of `ocaml/dune` to
```
(env
  (dev
    (flags    (:standard -w -a))))

(executable
 (name run_store_res)
 (libraries unix extraction hifirrtl_lang ocamlgraph mlir_lang)
 )
```
run :
```bash
docker run --rm esop-artifact ./compare_with_gurobi.sh # Docker
or
./compare_with_gurobi.sh # local
```

#### Expected Output
```bash
time cost : ...
value equal for ... = ...
...

The values of all variables match!
```

### Part 2: Compare with firtool
Change the file content of `ocaml/dune` to
```
(env
  (dev
    (flags    (:standard -w -a))))

(executable
 (name run_compare_firtool)
 (libraries unix extraction hifirrtl_lang ocamlgraph mlir_lang)
 )
```
For quick inference consistency check and efficiency comparison of the test cases provided in our article, just do this:
```bash
docker run --rm esop-artifact ./compare_with_firtool.sh # Docker
or
./compare_with_firtool.sh # local
```
This is just a demonstration on the simple FIRRTL program `AddNot.fir` in `ocaml/demo/AddNot.fir`. Similarly, you can replace the test files in the script with any of the test cases provided in `ocaml/demo/firrtl program` and `ocaml/demo/mlir`. (The files start with `designed` cannot be tested in this part, because these cannot be inferred by `firtool`.)

#### Expected Output
```bash
extraction time : ...
computation time : ...
total time : ...
components amount : ...
... has type ... in both file
... has type ... in both file
../ocaml/demo/firrtl program/AddNot.fir type check finished.
```

#### Note
We also support checking any other firrtl program. Before conducting the test, please obtain the latest release version of `firtool` from https://github.com/llvm/circt/releases.

```bash
# generate MLIR of your own FIRRTL proram
firtool --mlir-print-ir-after=firrtl-infer-widths ./your/path/to/example.fir &> ./where/you/want/to/put/example.mlir
# Ignore connection statements, retain definitions (under the `ocaml/ocaml_try` directory)
./process_mlir.sh ./where/you/want/to/put/example.mlir
```

Place your `example.fir` and `example.mlir` in `ocaml/demo/firrtl program` and `ocaml/demo/mlir` respectively, modify the corresponding file names in the script, and then execute `./compare_with_firtool.sh`.

## Artifact Structure & Code Guide

```
.
├── HiFirrtl.v                   # Syntax of HiFirrtl
├── LoFirrtl.v                   # Syntax of LoFirrtl
├── constraints.v                # Constraint definitions and some useful lemmas
├── extract_cswithmin.v          # Extract constraint from a firrtl circuit
├── scc.v                        # Formalization of our solving upper bound algorithm and its correctness proofs
├── branch_and_bound.v           # Formalization of our BaB algorithm and its correctness proofs
├── floyd_sc.v                   # Formalization of our adapted maximum path Floyd-Warshall algorithm and its correctness proofs
├── inferWidths.v                # Formalization of our width inference procedure and its correctness proofs
├── ocaml/
│   ├── hiparser/                # A HiFirrtl parser
│   ├── demo/                    # Paper evaluation benchmarks
│   ├── min_solver.ml            # Ocaml inferwidths compilation pass
│   └── ...
├── build_and_run.sh             # Script to run the ocaml inferwidth
├── compare_with_firtool.sh      # Script to reproduce the comparison result with firtool
├── compare_with_gurobi.sh       # Script to reproduce the comparison result with Gurobi
├── ...
```

**Key Files:**
- `branch_and_bound.v`: Contains `Proposition 2` proof, Formalizes the `BaB` algorithm and its correctness proof.
Theorem `smaller_sol_is_sol` : Section 2.2 , `Proposition 2`.
Function `bab_bin` : Section 3.3, Section 4.1(`BaB`).
Theorem `bab_bin_correct1`, Theorem `bab_bin_correct2` : Section 4.2(`P_BaB`).

- `scc.v` : Formalizes `Proposition 3`.
Definition `solve_ubs_aux` : Section 3.2, `Proposition 3`.

- `floyd_sc.v` : Formalizes the `maximum Floys-Warshall` algorithm and its correctness proof.
Function `solve_simple_cycle` : Section 3.4, Section 4.1(`inferSCC: nontrivial-maxfw`).
Lemma `scc_smallest`, Lemma `solve_simple_cycle_correctness` : Section 4.2(`P_maxFW`).

- `inferWidths.v` : Formalizes the complete width inference procedure and its correctness proof.
Definition `solve_scc` : Section 4.1(`inferSCC`)
Fixpoint `solve_alg` : Section 4.1(`inferWidth`)
Lemma `solve_scc_correctness`, Lemma `solve_scc_smallest`, Lemma `solve_scc_unsat` : Section 4.2(`P_inferSCC`)
Lemma `solve_alg_correctness`, Lemma `solve_alg_smallest`, Lemma `solve_alg_return_unsat` : Section 4.2(`P_inferWidth`)

## 🛠️ Troubleshooting

**Common Issues:**
- **Network problem during building docker**: Try `docker pull ocaml/opam:debian-11-ocaml-4.14` before build.
- **Permission denied**: Try `chmod -R 777 your/file`
- **Gurobi license errors**: Ensure academic network connection or configure license file
- **Coq compilation errors**: Check Coq version is exactly 8.16.0

**Getting Help:**
- Contact: `wangky@ios.ac.cn`