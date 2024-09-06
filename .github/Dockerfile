FROM coqorg/coq:8.20-ocaml-4.14-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

RUN opam repo add coq-released https://coq.inria.fr/opam/released \
    && opam update \
    && opam install coq-equations coq-menhirlib menhir ppx_inline_test \
    && eval $(opam env)
