#!/bin/bash

set -e

# Step1: generate Makefile
coq_makefile -f _CoqProject -o Makefile

# Step2: init Dune project
dune init proj ocaml_try

# Step3: Copy OCaml related files
cp -r ./ocaml/{extraction,hiparser,mlirparser} ./ocaml_try/
cp ./ocaml/{dune,inline.ml,min_solver.ml,nodehelper.ml,printfir.ml,run_solver.ml,transhiast.ml,useocamlscc.ml} ./ocaml_try/

# Step4: compile Coq project
make
echo -e "✅ Coq formalization compiled successfully"

# Step5: build OCaml project
cd ocaml_try
dune build
echo -e "✅ OCaml implementation built"
echo -e "🚀 Running demo on sample circuit..."

# Step6: run test
./_build/default/run_solver.exe ../ocaml/demo/AddNot.fir
echo -e "🎉 Smoke test completed successfully!"
