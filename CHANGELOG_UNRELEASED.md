# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemma `globally0`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`
- in `measure.v`:
  + lemma `measurable_fun_bigcup`
- in `sequences.v`:
  + lemma `eq_eseriesl`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_expR`

### Changed

- in `lebesgue_measure.v`
  + `measurable_funrM`, `measurable_funN`, `measurable_fun_exprn`

### Renamed

- in `derive.v`:
  + `Rmult_rev` -> `mulr_rev`
  + `rev_Rmult` -> `rev_mulr`
  + `Rmult_is_linear` -> `mulr_is_linear`
  + `Rmult_linear` -> `mulr_linear`
  + `Rmult_rev_is_linear` -> `mulr_rev_is_linear`
  + `Rmult_rev_linear` -> `mulr_rev_linear`
  + `Rmult_bilinear` -> `mulr_bilinear`
  + `is_diff_Rmult` -> `is_diff_mulr`

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemma `measurable_fun_sqr` (use `measurable_fun_exprn` instead)
  + lemma `measurable_fun_opp` (use `measurable_funN` instead)

### Removed

- in `normedtype.v`:
  + instance `Proper_dnbhs_realType`
- in `measure.v`:
  + instances `ae_filter_algebraOfSetsType`, `ae_filter_measurableType`,
  `ae_properfilter_measurableType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_funN` (use `measurable_funT_comp`) instead

### Infrastructure

### Misc
