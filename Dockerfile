# 基础镜像（Debian版本）
FROM ocaml/opam:debian-11-ocaml-4.14

# 安装系统级依赖
RUN sudo apt-get update && \
    sudo apt-get install -y --no-install-recommends \
    m4 \
    pkg-config \
    libgmp-dev 

# 设置OPAM环境
RUN opam repo add coq-released https://coq.inria.fr/opam/released

# 在安装 Coq 前添加内存优化步骤
RUN opam install -y depext && \
    opam depext -y coq.8.16.0

# 使用单线程编译 (-j 1) 减少内存压力
RUN opam install -y -j 1 coq=8.16.0 && \
    opam pin add coq 8.16.0 

# 安装Coq相关依赖
RUN opam install -y \
    coq-mathcomp-algebra=2.2.0 \
    coq-mathcomp-fingroup=2.2.0 \
    coq-mathcomp-ssreflect=2.2.0 \
    coq-mathcomp-tarjan=1.0.2

# 安装OCaml依赖
RUN opam install -y \
    ocamlgraph=2.1.0 

# 设置工作目录
WORKDIR /app

# 复制项目文件
COPY . .

# 验证入口点
#CMD ["sh", "-c", "mkdir ocaml_try && cd ocaml_try && ls ../ocaml/demo"]
CMD ["sh", "-c", "./build_and_run.sh"]
#CMD []
