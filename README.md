Analysis library compatible with Mathematical Components
========================================================

[![Join the chat at https://gitter.im/math-comp/analysis](https://badges.gitter.im/math-comp/analysis.svg)](https://gitter.im/math-comp/analysis?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
[![Travis](https://travis-ci.org/math-comp/analysis.svg?branch=master)](https://travis-ci.org/math-comp/analysis)
![Cachix](https://github.com/math-comp/analysis/workflows/Cachix/badge.svg)

## Disclaimer

This library is still at an early and experimental stage.
Contents may change, definitions and theorems may be renamed,
and inference mechanisms may be replaced at any major version bump.
Use at your own risk.

## Contents

This repository contains an experimental library for real analysis
for the Coq proof-assistant and using the Mathematical Components
library.

It is inspired by the [Coquelicot library]. The instantiation of the
mathematical structures of the Mathematical Components library with
the real numbers of the standard Coq library uses a well-known file
(Rstruct.v) from the [CoqApprox library] (with modifications from various
authors).

[Coquelicot library]: http://coquelicot.saclay.inria.fr/
[CoqApprox library]: http://tamadi.gforge.inria.fr/CoqApprox/

## Contributing

Always submit a pull request for code and wait for the CI to pass before merging.
Text markup files may be edited directly though, should you have commit rights.

## License

The license for this library's original contents is [CeCILL-C].

[CeCILL-C]: http://www.cecill.info/index.en.html

## Authors

see [AUTHORS.md](AUTHORS.md)

## Files

see [FILES.md](FILES.md)

## Requirements and Installation Procedure

see [INSTALL.md](INSTALL.md)

## Developping with nix

see [NIX.md](NIX.md)
