# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemmas `gt0_fin_numE`, `lt0_fin_numE`

- in `charge.v`:
  + factory `isCharge`

- in `measure.v`:
  + lemmas `negligibleI`, `negligible_bigsetU`, `negligible_bigcup`

### Changed

- in `hoelder.v`:
  + definition `Lnorm` now `HB.lock`ed

- in `measure.v`:
  + order of parameters changed in `semi_sigma_additive_is_additive`,
    `isMeasure`

### Renamed

- in `charge.v`
  + `isCharge` -> `isSemiSigmaAdditive`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

### Deprecated

### Removed

### Infrastructure

### Misc
