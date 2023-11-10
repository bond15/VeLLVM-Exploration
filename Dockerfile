FROM coqorg/coq:8.15.2-ocaml-4.13.1-flambda
USER root

RUN sudo apt-get update
RUN sudo apt-get install -y clang

#USER coq
RUN chown -R root: /home/coq
RUN rm -rf /home/coq
#ENV PATH="${PATH}:/home/coq/.opam/4.13.1+flambda/bin:/home/coq/.local/bin:/home/coq/bin"

RUN sudo opam init --disable-sandboxing --compiler ocaml-base-compiler.4.13.1
#RUN opam switch create vellvm ocaml-base-compiler.4.13.1
RUN opam repo add coq-released https://coq.inria.fr/opam/released


RUN opam pin add coq 8.15.2 -y
RUN opam install coq-ext-lib -y
RUN opam install coq-paco
RUN opam install coq-itree
RUN opam pin coq-flocq 3.4.3 -y
RUN opam install coq-ceres
RUN opam install coq-mathcomp-ssreflect
RUN opam install coq-simple-io -y

RUN opam install ocamlbuild
RUN opam install dune
RUN opam install menhir -y
RUN opam install qcheck -y

#USER root

RUN git clone --branch dev --recurse-submodule https://github.com/vellvm/vellvm.git

ENV PATH="${PATH}:/root/.opam/ocaml-base-compiler.4.13.1/bin"

# I ran the following from within the container and they worked
WORKDIR /home/coq/vellvm/lib/QuickChick
RUN make

WORKDIR /home/coq/vellvm/lib/flocq-quickchick
RUN make

WORKDIR /home/coq/vellvm/lib/coq2html
RUN make

WORKDIR /home/coq/vellvm/src 
RUN make

