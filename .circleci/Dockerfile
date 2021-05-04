FROM coqorg/coq:dev-ocaml-4.11-flambda
ENV OPAMYES true
RUN opam update \
 && opam install -j `nproc` \
         coq-quickchick \
         coq-vst
