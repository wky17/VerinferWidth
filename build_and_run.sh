#!/bin/bash

# 在遇到错误时退出脚本
set -e

# 步骤1: 生成Makefile
coq_makefile -f _CoqProject -o Makefile

# 步骤2: 初始化Dune项目
dune init proj ocaml_try

# 步骤3: 创建必要的目录
mkdir -p ocaml_try/extraction

# 步骤4: 编译Coq项目
make

# 步骤5: 移动OCaml相关文件
mv ./ocaml/{hiparser,mlirparser,dune,inline.ml,min_solver.ml,nodehelper.ml,printfir.ml,run_solver.ml,transhiast.ml,useocamlscc.ml} ./ocaml_try

# 步骤6: 移动extraction配置文件
mv ./ocaml/extraction/dune ./ocaml_try/extraction/

# 步骤7: 进入项目目录并构建
cd ocaml_try
dune build

# 步骤8: 运行测试程序
./_build/default/run_solver.exe ../ocaml/demo/AddNot.fir