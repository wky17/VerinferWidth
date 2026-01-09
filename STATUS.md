# Artifact Evaluation Status

## Badges Applied For

*   **Functional**
*   **Reusable**
*   **Available**

## Justifications

### Functional
We apply for the **Functional** badge because our artifact, VerinferWidth implementing the algorithm described in the paper, meets all the required criteria:

1.  **Documented:** The artifact is comprehensively documented in the accompanying `README` file. This includes clear instructions for installation, setup, configuration, and execution of all major functionalities and experiments presented in the paper. We detail the required dependencies and environment.
2.  **Consistent:** The artifact consistently produces the results reported in the paper **A Formally Verified Procedure for Width Inference in FIRRTL** when executed according to the provided instructions and using the supplied data.
3.  **Complete:** The artifact package includes all essential components: the core source code, example input data used in the paper's evaluation and scripts to replicate key experiments (e.g., `build_and_run.sh`, `compare_with_firtool.py`, `compare_with_gurobi.py`).
4.  **Exercisable:** The artifact is readily executable. We provide a Docker image (`Dockerfile`) and clear instructions for native installation. Users can successfully install, run the main functionalities, and reproduce the core experiments.
5.  **Evidence of Verification & Validation:** The artifact incorporates evidence demonstrating its correctness and robustness. This includes proofs of key properties, e.g., Section 2.2 Proposition 2 (`branch_and_bound.v` Theorem smaller_sol_is_sol), Section 4.2 P_inferSCC (`inferWidths.v` Lemma solve_scc_correctness, solve_scc_smallest, solve_scc_unsat), Section 4.2 P_inferWidth (`inferWidths.v` Lemma solve_alg_correctness, solve_alg_smallest, solve_alg_return_unsat). We also provide scripts verifying output against expected results (e.g., `build_and_run.sh`, `compare_with_firtool.py`, `compare_with_gurobi.py`).

### Reusable
We apply for the **Reusable** badge because our artifact significantly exceeds minimal functionality, demonstrating high quality that facilitates reuse:

1.  **Exceeds Functional Standards:** Beyond meeting all Functional criteria, the artifact is engineered with reusability as a core principle.
2.  **Careful Documentation:** The documentation (`README`) goes beyond basic usage. It includes:
    *   A clear, modular **Artifact Structure & Code Guide** explaining the architecture and key components.
    *   Comprehensive **Getting Started Guide** illustrating common usage scenarios beyond the paper's specific experiments.
    *   **Guidelines for extension and modification** are provided for users to conduct tests on their own examples and the output results of our tool are programs that conform to the FIRRTL syntax, they can still be operated by other tools.
3.  **Well-Structured Code/Design:** The source code is **modularly organized** and **clean and well-commented** following consistent coding standards.
4.  **Facilitates Repurposing:** The artifact's design, documentation, and included examples make it straightforward for other researchers to:
    *   Understand its inner workings.
    *   Integrate components into their own workflows.
    *   Adapt it to solve related problems or conduct new experiments.

### Available
We apply for the **Available** badge because:

1.  **Archival Repository:** The artifact relevant to the paper **A Formally Verified Procedure for Width Inference in FIRRTL** has been deposited in the **[Repository Name - e.g., Zenodo, FigShare, Dryad]** public archival repository.
2.  **Permanent Accessibility:** This repository guarantees long-term preservation and permanent accessibility through its stated policies and infrastructure.
3.  **DOI Provided:** The artifact has been assigned the permanent Digital Object Identifier (DOI) and is submitted as a link for AE.
4.  **CR Paper Inclusion:** This DOI will be included in the Camera-Ready version of our paper.