FROM ocaml/opam:debian-11-ocaml-4.14

RUN sudo apt-get update && \
    sudo apt-get install -y --no-install-recommends \
    m4 \
    pkg-config \
    libgmp-dev 

RUN sudo apt install -y python3
RUN sudo apt install -y python3-pip
RUN pip install gurobipy

RUN opam repo add coq-released https://coq.inria.fr/opam/released

RUN opam install -y depext && \
    opam depext -y coq.8.16.0

RUN opam install -y -j 1 coq=8.16.0 && \
    opam pin add coq 8.16.0 

RUN opam install -y \
    coq-mathcomp-algebra=2.2.0 \
    coq-mathcomp-fingroup=2.2.0 \
    coq-mathcomp-ssreflect=2.2.0 \
    coq-mathcomp-tarjan=1.0.2

RUN opam install -y \
    ocamlgraph=2.1.0 

WORKDIR /app

COPY . .

#CMD ["sh", "-c", "mkdir ocaml_try && cd ocaml_try && ls ../ocaml/demo"]
#CMD ["sh", "-c", "./build_and_run.sh"]
CMD []
