# REQUIREMENTS for [A Formally Verified Procedure for Width Inference in FIRRTL] Artifact

## 1. Hardware Architecture
- **Minimum RAM**: 8GB (16GB recommended for complex proofs)
- **Disk Space**: 5GB minimum (for dependencies and build artifacts)

## 2. Software Requirements (Native Environment)
*For users not using Docker - RECOMMENDED to use Docker instead*

### Base System
- **Operating System**: macOS ≥12 (Monterey), Linux (Ubuntu 22.04/Debian 11+)
- **Package Manager**: Homebrew (macOS), apt (Linux)

### Core Dependencies
- [Coq](https://coq.inria.fr) = 8.16.0
- [Mathematical Components](https://math-comp.github.io) (MathComp) = 2.2.0
- [MathComp-tarjan](https://github.com/coq-community/tarjan) = 1.0.2
- [OCaml](https://ocaml.org) = 4.14.2
- [OCamlgraph](https://github.com/backtracking/ocamlgraph) = 2.1.0
- [dune](https://dune.build) = 3.16.0

### Optional Components for reproduction
- [Gurobi Optimizer](https://www.gurobi.com) = 12.0.1 (requires academic license)
- [CIRCT](https://circt.llvm.org) (LLVM-based hardware design toolchain)

## 3. Docker Environment (RECOMMENDED)
The provided Dockerfile creates a reproducible environment with all dependencies.

### Docker Specifications
- **Base Image**: `ocaml/opam:debian-ocaml-4.14`
- **To be installed**:
  - Coq 8.16.0
  - MathComp 2.2.0 + tarjan 1.0.2
  - OCamlgraph 2.1.0
  - dune 3.16.0
  - Gurobi 12.0.1 
