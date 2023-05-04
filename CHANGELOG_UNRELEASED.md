# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemma `globally0`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`

- in file `topology.v`,
  + definitions `discrete_ent`, `discrete_ball`, `discrete_topology`
    and `pseudoMetric_bool`.
  + lemmas `finite_compact`, `discrete_ball_center`, `compact_cauchy_cvg`

- in `measure.v`:
  + lemma `measurable_fun_bigcup`
- in `sequences.v`:
  + lemma `eq_eseriesl`

- in file `topology.v`,
  + new definitions `basis`, and `second_countable`.
  + new lemmas `clopen_countable` and `compact_countable_base`.
- in `classical_sets.v`:
  + lemmas `set_eq_le`, `set_neq_lt`
- in `set_interval.v`:
  + lemma `set_lte_bigcup`
- in `lebesgue_integral.v`:
  + lemmas `emeasurable_fun_lt`, `emeasurable_fun_le`, `emeasurable_fun_eq`,
    `emeasurable_fun_neq`
  + lemma `integral_ae_eq`

### Changed

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

### Removed

- in `normedtype.v`:
  + instance `Proper_dnbhs_realType`
- in `measure.v`:
  + instances `ae_filter_algebraOfSetsType`, `ae_filter_measurableType`,
  `ae_properfilter_measurableType`
- in `lebesgue_integral.v`
  + lemma `emeasurable_funN` (already in `lebesgue_measure.v`)

### Infrastructure

### Misc
