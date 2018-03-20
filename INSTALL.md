# Installing

## Requirements
- [Coq version 8.7.2](https://github.com/coq/coq)
- [Mathematical Components development version](https://github.com/math-comp/math-comp)

These requirements can be installed in a custom way or through opam using the repository https://coq.inria.fr/opam/extra-dev, which you can add by typing `opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev`

## Instructions
- Custom:
  + Type `make` to use the provided `Makefile`.
- Through opam (assuming `opam` has been properly configured and `extra-dev` repository is added):
  + Type `opam pin add coq-mathcomp-analysis .`
