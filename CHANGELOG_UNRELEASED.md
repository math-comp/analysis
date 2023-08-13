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

- in `charge.v`
  + replace old isCharge.Build to isSemiSigmaAdditive.Build in section `charge_restriction`
  + replace to new isCharge.Build in the others

### Renamed

- in `charge.v`
  + old `isCharge` renamed to `isSemiSigmaAdditive`
  + old `Charge` renamed to `AdditiveCharge_SemiSigmaAdditive_isCharge`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

### Deprecated

### Removed

### Infrastructure

### Misc
