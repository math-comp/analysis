# Changelog (unreleased)

## [Unreleased]

### Added

- in `num_topology.v`:
  + lemma `in_continuous_mksetP`

- in `normedtype.v`:
  + lemmas `continuous_within_itvcyP`, `continuous_within_itvNycP`

- in `mathcomp_extra.v`:
  + lemma `partition_disjoint_bigfcup`
- in `lebesgue_measure.v`:
  + lemma `measurable_indicP`

- in `lebesgue_integral.v`:
  + definition `dyadic_approx` (was `Let A`)
  + definition `integer_approx` (was `Let B`)
  + lemma `measurable_sum`
  + lemma `integrable_indic`

- in `constructive_ereal.v`:
  + notations `\prod` in scope ereal_scope
  + lemmas `prode_ge0`, `prode_fin_num`

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`
  
### Renamed

- in `lebesgue_measure.v`:
  + `measurable_fun_indic` -> `measurable_indic`
  + `emeasurable_fun_sum` -> `emeasurable_sum`
  + `emeasurable_fun_fsum` -> `emeasurable_fsum`
  + `ge0_emeasurable_fun_sum` -> `ge0_emeasurable_sum`
- in `measure.v`:
  + `dynkin_setI_bigsetI` -> `setT_setI_bigsetI`

### Generalized

### Deprecated

- in file `lebesgue_integral.v`:
  + lemma `approximation`

### Removed

- in `lebesgue_integral.v`:
  + lemma `measurable_indic` (was uselessly specializing `measurable_fun_indic` (now `measurable_indic`) from `lebesgue_measure.v`)
  + notation `measurable_fun_indic` (deprecation since 0.6.3)

### Infrastructure

### Misc
