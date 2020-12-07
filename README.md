# Analysis library compatible with Mathematical Components

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/math-comp/analysis/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/math-comp/analysis/actions?query=workflow%3ACI




This repository contains an experimental library for real analysis for
the Coq proof-assistant and using the Mathematical Components library.

## Meta

- Author(s):
  - Reynald Affeldt (initial)
  - Cyril Cohen (initial)
  - Assia Mahboubi (initial)
  - Damien Rouhling (initial)
  - Pierre-Yves Strub (initial)
- License: [CeCILL-C](LICENSE)
- Compatible Coq versions: Coq 8.11 to 8.12
- Additional dependencies:
  - [MathComp field 1.11](https://math-comp.github.io)
  - [MathComp finmap 1.5](https://github.com/math-comp/finmap)
  - [Hierarchy Builder 0.10](https://github.com/math-comp/hierarchy-builder)
- Coq namespace: `mathcomp.analysis`
- Related publication(s):
  - [Formalization Techniques for Asymptotic Reasoning in Classical Analysis](https://jfr.unibo.it/article/view/8124) doi:[10.6092/issn.1972-5787/8124](https://doi.org/10.6092/issn.1972-5787/8124)
  - [Competing inheritance paths in dependent type theory---a case study in functional analysis](https://hal.inria.fr/hal-02463336) doi:[10.1007/978-3-030-51054-1_1](https://doi.org/10.1007/978-3-030-51054-1_1)
  - [Outils pour la Formalisation en Analyse Classique](http://www-sop.inria.fr/members/Damien.Rouhling/data/phd/thesis.pdf) 

## Building and installation instructions

The easiest way to install the latest released version of Analysis library compatible with Mathematical Components
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-analysis
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/analysis.git
cd analysis
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Disclaimer

This library is still at an experimental stage.  Contents may
change, definitions and theorems may be renamed, and inference
mechanisms may be replaced at any major version bump.  Use at your
own risk.

## Documentation

[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/237666-math-comp-analysis)

Each file is documented in its header.

Changes are documented in [CHANGELOG.md](CHANGELOG.md) and
[CHANGELOG_UNRELEASED.md](CHANGELOG_UNRELEASED.md).

[ORIGINAL_FILES.md](ORIGINAL_FILES.md) gives more details about the
files in the first releases.

Overview presentation: [Classical Analysis with Coq](https://perso.crans.org/cohen/CoqWS2018.pdf) (2018)

Other work using MathComp-Analysis: [A Formal Classical Proof of Hahn-Banach in Coq](https://lipn.univ-paris13.fr/~kerjean/slides/slidesTYPES19.pdf) (2019)

## Related work

This library is inspired by the [Coquelicot library](http://coquelicot.saclay.inria.fr/).
The instantiation of the mathematical structures of the Mathematical Components library
with the real numbers of the standard Coq library uses a well-known file (`Rstruct.v`)
from the [CoqApprox library](http://tamadi.gforge.inria.fr/CoqApprox/) (with
modifications from various authors).

## Development

[Requirements and Installation Procedure](INSTALL.md)

[Developping with nix](NIX.md)

[Contributing](CONTRIBUTING.md)

## Acknowledgments

Many thanks to [various contributors](https://github.com/math-comp/analysis/graphs/contributors)
