#!/bin/bash

# 在遇到错误时退出脚本
set -e

# 步骤1: 生成Makefile
coq_makefile -f _CoqProject -o Makefile

# 步骤2: 初始化Dune项目
dune init proj ocaml_try

# 步骤3: 拷贝OCaml相关文件
cp -r ./ocaml/{extraction,hiparser,mlirparser} ./ocaml_try/
cp ./ocaml/{dune,inline.ml,min_solver.ml,nodehelper.ml,printfir.ml,run_solver.ml,transhiast.ml,useocamlscc.ml} ./ocaml_try/

# 步骤4: 编译Coq项目
make
echo -e "✅ Coq formalization compiled successfully"

# 步骤5: 进入项目目录并构建
cd ocaml_try
dune build
echo -e "✅ OCaml implementation built"
echo -e "🚀 Running demo on sample circuit..."

# 步骤6: 运行测试程序
./_build/default/run_solver.exe ../ocaml/demo/AddNot.fir
echo -e "🎉 Smoke test completed successfully!"
