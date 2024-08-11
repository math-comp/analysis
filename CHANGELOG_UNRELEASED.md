# Changelog (unreleased)

## [Unreleased]

### Added

- in `derive.v`:
  + lemma `derive_id`
  + lemmas `exp_derive`, `exp_derive1`
  + lemma `derive_cst`
  + lemma `deriveMr`, `deriveMl`

- in `functions.v`:
  + lemmas `mull_funE`, `mulr_funE`

### Changed

### Renamed

- in `lebesgue_measure.v`:
  + `measurable_exprn` -> `exprn_measurable`
  + `measurable_mulrl` -> `mulrl_measurable`
  + `measurable_mulrr` -> `mulrr_measurable`
  + `measurable_fun_pow` -> `measurable_funX`
  + `measurable_oppe` -> `oppe_measurable`
  + `measurable_abse` -> `abse_measurable`
  + `measurable_EFin` -> `EFin_measurable`
  + `measurable_oppr` -> `oppr_measurable`
  + `measurable_normr` -> `normr_measurable`

### Generalized

- in `derive.v`:
  + lemma `derivable_cst`

### Deprecated

### Removed

- in `lebesgue_measure.v`:
  + notation `measurable_fun_sqr` (was deprecated since 0.6.3)
  + notation `measurable_fun_exprn` (was deprecated since 0.6.3)
  + notation `measurable_funrM` (was deprecated since 0.6.3)
  + notation `emeasurable_fun_minus` (was deprecated since 0.6.3)
  + notation `measurable_fun_abse` (was deprecated since 0.6.3)
  + notation `measurable_fun_EFin` (was deprecated since 0.6.3)
  + notation `measurable_funN` (was deprecated since 0.6.3)
  + notation `measurable_fun_opp` (was deprecated since 0.6.3)
  + notation `measurable_fun_normr` (was deprecated since 0.6.3)

### Infrastructure

### Misc
