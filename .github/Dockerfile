FROM coqorg/coq:8.20-ocaml-4.14-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

RUN opam repo add coq-released https://coq.inria.fr/opam/released \
    && opam update \
    && opam install coq-equations coq-menhirlib menhir ppx_expect \
    && eval $(opam env)

RUN sudo apt-get update -y -q \
    && DEBIAN_FRONTEND=noninteractive sudo apt-get install -y -q --no-install-recommends pandoc
