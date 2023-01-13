# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + canonical `unit_pointedType`
- in `measure.v`:
  + definition `finite_measure`
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`

- in `constructive_ereal.v`:
  + lemma `oppe_inj`

- in `mathcomp_extra.v`:
  + lemma `add_onemK`
  + function `swap`
- in `classical_sets.v`:
  + lemmas `setT0`, `set_unit`, `set_bool`
  + lemmas `xsection_preimage_snd`, `ysection_preimage_fst`
- in `exp.v`:
  + lemma `expR_ge0`
- in `measure.v`
  + lemmas `measurable_curry`, `measurable_fun_fst`, `measurable_fun_snd`,
    `measurable_fun_swap`, `measurable_fun_pair`, `measurable_fun_if_pair`
  + lemmas `dirac0`, `diracT`
  + lemma `finite_measure_sigma_finite`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_opp`
- in `lebesgue_integral.v`
  + lemmas `integral0_eq`, `fubini_tonelli`

### Changed

- in `fsbigop.v`:
  + implicits of `eq_fsbigr`

### Renamed

- in `measurable.v`:
  + `measurable_fun_comp` -> `measurable_funT_comp`

### Generalized

- in `esum.v`:
  + lemma `esum_esum`
- in `measure.v`
  + lemma `measurable_fun_comp`
- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`

### Deprecated

### Removed

- in `esum.v`:
  + lemma `fsbig_esum`

### Infrastructure

### Misc
