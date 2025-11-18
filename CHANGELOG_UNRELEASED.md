# Changelog (unreleased)

## [Unreleased]

### Added

- in `measure_negligible.v`:
  + definition `null_set` with notation `_.-null_set`
  + lemma `subset_null_set`
  + lemma `negligible_null_set`
  + lemma `measure_null_setP`
  + definition `null_set_dominates`
  + lemma `null_dominates_trans`
  + lemma `null_dominatesP`

- in `charge.v`:
  + lemma `charge_null_dominatesP`

### Changed

- in `charge.v`:
  + `dominates_cscalel` specialized from
    `set _ -> \bar _` to `{measure set _ -> \bar _}`

- in `measurable_structure.v`:
  + the notation ``` `<< ``` is now for `null_set_dominates`,
    the previous definition can be recovered with the lemma
    `null_dominatesP`

### Renamed

- in `measure_negligible.v`:
  + `measure_dominates_ae_eq` -> `null_dominates_ae_eq`

- in `charge.v`:
  + `induced` -> `induced_charge`

### Generalized

### Deprecated

### Removed

- in `measurable_structure.v`:
  + definition `measure_dominates`
  + lemma `measure_dominates_trans`

### Infrastructure

### Misc
