# Installing

## Requirements

- [The Coq Proof Assistant version ≥ 8.13](https://coq.inria.fr)
- [Mathematical Components version ≥ 1.13.0](https://github.com/math-comp/math-comp)
- [Finmap library version ≥ 1.5.1](https://github.com/math-comp/finmap)
- [Hierarchy builder version >= 1.2.0](https://github.com/math-comp/hierarchy-builder)

These requirements can be installed in a custom way, or through
[opam](https://opam.ocaml.org/) (the recommended way) using
the repository https://coq.inria.fr/opam/released, which you can add by typing
`opam repo add coq-released https://coq.inria.fr/opam/released`.

Detailed instructions for possible installations of Mathematical Components are located
[here](https://github.com/math-comp/math-comp/blob/master/INSTALL.md).

## Short Instructions

- Through opam:
  + type `opam install coq-mathcomp-analysis.X.Y.Z` where `X.Y.Z` is the version number
    (all the dependencies should be automatically installed, assuming `opam` has been properly
    configured and `coq-released` repository is added)
- Custom (assuming the requirements are met):
  + type `make` to use the provided `Makefile`

## From scratch instructions

### How to install as a package

1. Install opam
- any linux system:
```
$ sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```

2. Configure opam
```
$ export OPAMROOT=~/.opam_mathcomp_analysis # opam configuration, metadata, logs, temporary directories and caches
$ opam init -j4 # adapt to the number of cores you have
$ eval `opam config env`
$ opam repo add coq-released https://coq.inria.fr/opam/released
```
3. Install our package (and all its dependencies)
```
$ opam install coq-mathcomp-analysis
```
To install a precise version, type, say
```
$ opam install coq-mathcomp-analysis.0.6.0
```
4. Everytime you want to work in this same context, you need to type
```
$ export OPAMROOT=~/.opam_mathcomp_analysis 
$ eval `opam config env`
```

### How to edit and test the source code

If you would rather edit and test the files than intalling them, we suggest that you replace
`opam install coq-mathcomp-analysis` command with the following
```
$ opam install coq-mathcomp-analysis --deps-only
$ git clone https://github.com/math-comp/analysis
$ cd analysis
$ make
```
You may then browse the files using `coqide` (you might want to `opam install coqide`) or
using [proof general for emacs](https://github.com/ProofGeneral/PG)

## Break-down of phase 3 of the installation procedure step by step

With the example of Coq 8.14.0 and MathComp 1.13.0. For other versions, update the
version numbers accordingly.

1. Install Coq 8.14.0
```
$ opam install coq.8.14.0
```
2. Install the Mathematical Components
```
$ opam install coq-mathcomp-ssreflect.1.13.0
$ opam install coq-mathcomp-fingroup.1.13.0
$ opam install coq-mathcomp-algebra.1.13.0
$ opam install coq-mathcomp-solvable.1.13.0
$ opam install coq-mathcomp-field.1.13.0
```
3. Install the Finite maps library
```
$ opam install coq-mathcomp-finmap.1.5.1
```
4. Install the Hierarchy Builder
```
$ opam install coq-hierarchy-builder.1.2.0
```
5. Download and compile `coq-mathcomp-analysis` without installing
```
$ git clone https://github.com/math-comp/analysis
$ cd analysis
$ make
```

## How to clean your computer

- If you installed the package `coq-mathcomp-analysis` and wish to get rid of it, just type
```
$ opam remove coq-mathcomp-analysis
```
- However if you wish to clean the entire installation (including `coq` and `mathcomp` dependencies)
  you should remove the opam root we created for this purpose:
```
$ rm -rf ~/.opam_mathcomp_analysis
```
