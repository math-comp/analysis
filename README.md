# Analysis library compatible with Mathematical Components

[![Nix CI][nix-action-shield]][nix-action-link]
[![Chat][chat-shield]][chat-link]

[nix-action-shield]: https://github.com/math-comp/analysis/actions/workflows/nix-action-master.yml/badge.svg?branch=master
[nix-action-link]: https://github.com/math-comp/analysis/actions?query=branch%3Amaster+event%3Apush

[chat-shield]: https://img.shields.io/badge/zulip-join_chat-brightgreen.svg
[chat-link]: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis

This repository contains a real analysis library for the Coq / Rocq proof-assistant.
It is based on the [Mathematical Components](https://math-comp.github.io/) library.

In terms of [opam](https://opam.ocaml.org/doc/Install.html), it comes as the following packages:
- `coq-mathcomp-classical`: a layer for classical reasoning
- `coq-mathcomp-reals`: real numbers for MathComp
- `coq-mathcomp-reals-stdlib`: compatibility with the real numbers of the Coq standard library
- `coq-mathcomp-analysis-stdlib`: compatibility with the Coq standard library (topology only)
- `coq-mathcomp-analysis`: theories for real analysis
- `coq-mathcomp-experimental-reals`: sequences of real numbers and distributions (experimental)

## Meta

- [Authors](AUTHORS.md)
- License: [CeCILL-C](LICENSE)
- Compatible Rocq versions: Coq 8.20, Rocq 9.0 (or dev)
- Additional dependencies:
  - [MathComp ssreflect 2.4.0 or later](https://math-comp.github.io)
  - [MathComp fingroup 2.4.0 or later](https://math-comp.github.io)
  - [MathComp algebra 2.4.0 or later](https://math-comp.github.io)
  - [MathComp solvable 2.4.0 or later](https://math-comp.github.io)
  - [MathComp field 2.4.0 or later](https://math-comp.github.io)
  - [MathComp finmap 2.1.0](https://github.com/math-comp/finmap)
  - [MathComp bigenough 1.0.0](https://github.com/math-comp/bigenough)
  - [Hierarchy Builder 1.8.0 or later](https://github.com/math-comp/hierarchy-builder)
- Coq/Rocq namespace: `mathcomp.analysis`

## Building and installation instructions

The easiest way to install the latest released version of MathComp-Analysis library is
via the [opam](https://opam.ocaml.org/doc/Install.html) package manager:

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-mathcomp-analysis
```
Note that the packages `coq-mathcomp-classical` and `coq-mathcomp-reals` will be installed as dependencies.

### Manual installation

To build and install manually, make sure that the dependencies are met and do:

``` shell
git clone https://github.com/math-comp/analysis.git
cd analysis
make   # or make -j <number-of-cores-on-your-machine>
make install
```

## Documentation

Each file is documented in its header in ASCII.

[HTML rendering of the source code](https://math-comp.github.io/analysis/htmldoc_1_14_0/index.html) (using [`rocqnavi`](https://github.com/affeldt-aist/rocqnavi)).
It includes inheritance diagrams for the mathematical structures that MathComp-Analysis adds on top of MathComp's ones.

Overview presentations:
- [Classical Analysis with Coq](https://perso.crans.org/cohen/CoqWS2018.pdf) (2018)
- [A selection of links to well-known lemmas](https://github.com/math-comp/analysis/wiki/What's-where%3F)
- [An Introduction to MathComp-Analysis](https://staff.aist.go.jp/reynald.affeldt/documents/karate-rocq.pdf) (2022-2025)

Publications about MathComp-Analysis:
- [Formalization Techniques for Asymptotic Reasoning in Classical Analysis](https://jfr.unibo.it/article/view/8124) (2018)
  doi:[10.6092/issn.1972-5787/8124](https://doi.org/10.6092/issn.1972-5787/8124)
- [Formalisation Tools for Classical Analysis](http://www-sop.inria.fr/members/Damien.Rouhling/data/phd/thesis.pdf) (2019)
- [Competing inheritance paths in dependent type theory---a case study in functional analysis](https://hal.inria.fr/hal-02463336) (2020)
  doi:[10.1007/978-3-030-51054-1_1](https://doi.org/10.1007/978-3-030-51054-1_1)
- [Measure Construction by Extension in Dependent Type Theory with Application to Integration](https://arxiv.org/pdf/2209.02345.pdf) (2023)
  doi:[10.1007/s10817-023-09671-5](https://doi.org/10.1007/s10817-023-09671-5)
- [The Radon-Nikodým Theorem and the Lebesgue-Stieltjes Measure in Coq](https://www.jstage.jst.go.jp/article/jssst/41/2/41_2_41/_pdf/-char/en) (2024)
  doi:[10.11309/jssst.41.2_41](https://doi.org/10.11309/jssst.41.2_41)
- [A Comprehensive Overview of the Lebesgue Differentiation Theorem in Coq](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.5/LIPIcs.ITP.2024.5.pdf) (2024)
- [Prouver que pi est irrationnel avec MathComp-Analysis](https://hal.science/hal-04859455/document) (2025)
- [Formalizing Concentration Inequalities in Rocq: Infrastructure and Automation](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.21) (2025)

Other work using MathComp-Analysis:
- [A Formal Classical Proof of Hahn-Banach in Coq](https://lipn.univ-paris13.fr/~kerjean/slides/slidesTYPES19.pdf) (2019)
- [Semantics of Probabilistic Programs using s-Finite Kernels in Coq](https://hal.inria.fr/hal-03917948/document) (2023)
  doi:[10.1145/3573105.357569](https://doi.org/10.1145/3573105.3575691)
- [CoqQ: Foundational Verification of Quantum Programs](https://arxiv.org/pdf/2207.11350.pdf) (2023)
  doi:[10.1145/3571222](https://doi.org/10.1145/3571222)
- [Experimenting with an intrinsically-typed probabilistic programming language in Coq](https://staff.aist.go.jp/reynald.affeldt/documents/syntax-aplas2023.pdf) (2023)
  doi:[10.1007/978-981-99-8311-7_9](https://doi.org/10.1007/978-981-99-8311-7_9)
- [Taming Differentiable Logics with Coq Formalisation](https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.4/LIPIcs.ITP.2024.4.pdf) (2024)
- [Décomposition Algébrique Cylindrique en Coq/Rocq](https://inria.hal.science/hal-04859512/document) (2025)
- [Semantics of Probabilistic Programs using s-Finite Kernels in Dependent Type Theory](https://dl.acm.org/doi/pdf/10.1145/3732291) (2025)
- [A Formal Foundation for Equational Reasoning on Probabilistic Programs](https://staff.aist.go.jp/reynald.affeldt/documents/eddy_aplas2025.pdf) (2025)
  doi:[10.1007/978-981-95-3585-9_3](https://doi.org/10.1007/978-981-95-3585-9_3)

## About the stability of this library

Changes are documented systematically in [CHANGELOG.md](CHANGELOG.md) and
[CHANGELOG_UNRELEASED.md](CHANGELOG_UNRELEASED.md).

We bump the minor part of the version number for breaking changes.

We use deprecation warnings to help transitioning to new versions.

We try to preserve backward compatibility as best as we can.

## Development information

[Detailed requirements and installation procedure](INSTALL.md)

[Developping with nix](https://github.com/math-comp/math-comp/wiki/Using-nix)

[Contributing](CONTRIBUTING.md)

## Previous work reused at the time of the first releases

This library was inspired by the [Coquelicot library](http://coquelicot.saclay.inria.fr/)
by Sylvie Boldo, Catherine Lelay, and Guillaume Melquiond.
In the first releases, `topology.v` and `normedtype.v` contained a reimplementation of the file
`Hierarchy.v` from the library Coquelicot.

The instantiation of the mathematical structures of the Mathematical Components library
with the real numbers of the standard Coq library used a well-known file (`Rstruct.v`)
from the [CoqApprox library](http://tamadi.gforge.inria.fr/CoqApprox/) (with
modifications by various authors).

The proof of Zorn's Lemma in `classical_sets.v` (NB: new filename) was a reimplementation
of the one by Daniel Schepler (https://github.com/coq-community/zorns-lemma) but it has been rewritten for version 1.3.0;
we also originally took inspiration from Schepler's work on topology (https://github.com/coq-community/topology) for parts
of `topology.v`.

[ORIGINAL_FILES.md](ORIGINAL_FILES.md) gives more details about the
files in the first releases.

## Acknowledgments

Many thanks to [various contributors](https://github.com/math-comp/analysis/graphs/contributors)
