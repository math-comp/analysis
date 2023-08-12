# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemmas `gt0_fin_numE`, `lt0_fin_numE`

- in `charge.v`:
  + factory `isCharge`

### Changed

- in `hoelder.v`:
  + definition `Lnorm` now `HB.lock`ed

### Renamed

- in `charge.v`
  + `isCharge` renamed to `isSemiSigmaAdditive`
  + `Charge` renamed to `AdditiveCharge_SemiSigmaAdditive_isCharge`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

### Deprecated

### Removed

### Infrastructure

### Misc
