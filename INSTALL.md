# Installing

## Requirements
- [The Coq Proof Assistant version ≥ 8.7](https://coq.inria.fr)
- [Mathematical Components development version](https://github.com/math-comp/math-comp)
- [Finmap library development version](https://github.com/math-comp/finmap)

These requirements can be installed in a custom way or through [opam 1.2](https://opam.ocaml.org/) using the repository https://coq.inria.fr/opam/extra-dev, which you can add by typing `opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev`.

Detailed instructions for possible installations of Mathematical Components are located [here](https://github.com/math-comp/math-comp/blob/master/INSTALL.md).

## Short Instructions
- Custom (assuming Coq ≥ 8.7 and Mathematical Components `master` branch have been installed):
  + Type `make` to use the provided `Makefile`.
- Through opam:
  + Type `opam install coq-mathcomp-analysis`
  (all the dependencies should be automatically installed, assuming `opam` has been properly configured and `extra-dev` repository is added)

## From scratch instructions (assuming Debian based distribution)
### How to install as a package
From scratch with a Debian based linux distribution, here is what you should type:
```
$ sudo apt-get install opam
$ export OPAMROOT=~/.opam_mathcomp_analysis
$ opam init -j4 # adapt to the number of cores you have
$ eval `opam config env`
$ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
$ opam install coq-mathcomp-analysis
```

Then you need to type
```
$ export OPAMROOT=~/.opam_mathcomp_analysis 
$ eval `opam config env`
```
everytime you want to work in the same context

### How to edit and test the source code
If you would rather edit and test the files than intalling them, we suggest that you replace the `opam install coq-mathcomp-analysis` command with the following
```
$ opam install coq-mathcomp-analaysis --deps-only
$ git clone https://github.com/math-comp/analysis
$ cd analysis
$ make
```
You may then browse the files using `coqide` (you might want to `opam install coqide`) or using [proof general for emacs](https://github.com/ProofGeneral/PG)

## From scratch instructions break-down (Debian based)
1. Install and configure opam
```
$ sudo apt-get install opam
$ export OPAMROOT=~/.opam_mathcomp_analysis
$ opam init -j4 # adapt to the number of cores you have
$ eval `opam config env`
$ opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
```
2. Install Coq 8.7.2
```
$ opam install coq.8.7.2
```
3. Install Mathematical Components development version 
```
$ opam install coq-mathcomp-ssreflect.dev
$ opam install coq-mathcomp-fingroup.dev
$ opam install coq-mathcomp-algebra.dev
$ opam install coq-mathcomp-solvable.dev
$ opam install coq-mathcomp-field.dev
$ opam install coq-mathcomp-real_closed.dev
```
4. Install Finite maps library
```
$ opam install coq-mathcomp-finmap.dev
```
5. Download and compile `coq-mathcomp-analysis` without installing
```
$ git clone https://github.com/math-comp/analysis
$ cd analysis
$ make
```
## How to clean you computer
- If you installed the package `coq-mathcomp-analysis` and wish to get rid of it, just type
```
$ opam remove coq-mathcomp-analysis
```
- However if you wish to clean the entire installation (including `coq` and `mathcomp` dependencies) you should remove the opam root we created for this purpose:
```
$ rm -rf ~/.opam_mathcomp_analysis
```
