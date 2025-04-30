# Changelog (unreleased)

## [Unreleased]

### Added

- in new file `gauss_integral_alternative`
  + add lemmas `integral0y_gauss_fin_num`,
               `integral0y_u0`,
	       `integrable0y_u`,
	       `max_y_ge0`,
	       `u_dominates`,
	       `int0yu_fin_num`,
	       `cvgy_int0yu0`,
	       `dint0yuE`,
	       `derivable_int0yu`,
	       `rc_int0yu0`,
	       `gauss_integration`
- in `probability.v`:
  + lemmas `eq_bernoulli`, `eq_bernoulliV2`

- in `measure.v`:
  + lemmas `mnormalize_id`, `measurable_fun_eqP`

- in `ftc.v`:
  + lemma `integrable_locally`

- in `constructive_ereal.v`:
  + lemma `EFin_bigmax`

- in `mathcomp_extra.v`:
  + lemmas `inr_inj`, `inl_inj`

- in `classical_sets.v`:
  + lemmas `in_set1`, `inr_in_set_inr`, `inl_in_set_inr`, `mem_image`, `mem_range`, `image_f`
  + lemmas `inr_in_set_inl`, `inl_in_set_inl`

- in `lebesgue_integral_approximation.v` (now `measurable_fun_approximation.v`):
  + lemma `measurable_prod`
  + lemma `measurable_fun_lte`
  + lemma `measurable_fun_lee`
  + lemma `measurable_fun_eqe`
  + lemma `measurable_poweR`

- in `exp.v`:
  + lemma `poweRE`

- in `exp.v`:
  + lemmas `lnNy`, `powR_cvg0`, `derivable_powR`, `powR_derive1`
  + Instance `is_derive1_powR`
- in `realfun.v`:
  + lemma `cvge_ninftyP`

### Changed

- in `pi_irrational`:
  + definition `rational`

### Renamed

- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`

- in `lebesgue_integral_approximation.v`:
  + `emeasurable_fun_lt` -> `measurable_lte`
  + `emeasurable_fun_le` -> `measurable_lee`
  + `emeasurable_fun_eq` -> `measurable_lee`
  + `emeasurable_fun_neq` -> `measurable_neqe`

- file `lebesgue_integral_approximation.v` -> `measurable_fun_approximation.v`

### Generalized

- in `normedtype.v`:
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`

### Deprecated

### Removed

### Infrastructure

### Misc
