# Installing

## Requirements
- [The Coq Proof Assistant version ≥ 8.7](https://coq.inria.fr)
- [Mathematical Components development version](https://github.com/math-comp/math-comp)
- [Finmap library development version](https://github.com/math-comp/finmap)

These requirements can be installed in a custom way or through [opam 1.2](https://opam.ocaml.org/) using the repository https://coq.inria.fr/opam/extra-dev, which you can add by typing `opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev`.

Detailed instructions for possible installations of Mathematical Components are located [here](https://github.com/math-comp/math-comp/blob/master/INSTALL.md).

## Instructions
- Custom (assuming Coq ≥ 8.7 and Mathematical Components `master` branch have been installed):
  + Type `make` to use the provided `Makefile`.
- Through opam (assuming `opam` has been properly configured and `extra-dev` repository is added):
  + Type `opam pin add coq-mathcomp-analysis .`
