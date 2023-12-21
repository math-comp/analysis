# Changelog (unreleased)

## [Unreleased]

### Added

- in file `cantor.v`,
  + new definitions `cantor_space`, `cantor_like`, `pointed_discrete`, and 
    `tree_of`.
  + new lemmas `cantor_space_compact`, `cantor_space_hausdorff`, 
    `cantor_zero_dimensional`, `cantor_perfect`, `cantor_like_cantor_space`, 
    `tree_map_props`, `homeomorphism_cantor_like`, and 
    `cantor_like_finite_prod`.
  + new theorem `cantor_surj`.
- in file `topology.v`,
  + new lemmas `perfect_set2`, and `ent_closure`.
  + lemma `clopen_surj`

- in `cantor.v`:
  + definitions `pointed_principal_filter`,
    `pointed_discrete_topology`
  + lemma `discrete_pointed`
  + lemma `discrete_bool_compact`
- in `normedtype.v`:
  + hints for `at_right_proper_filter` and `at_left_proper_filter`

- in `realfun.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`,
    `increasing_fun`, `decreasing_fun`
  + lemmas `cvg_addrl`, `cvg_addrr`, `cvg_centerr`, `cvg_shiftr`,
    `nondecreasing_cvgr`,
	`nonincreasing_at_right_cvgr`,
	`nondecreasing_at_right_cvgr`,
	`nondecreasing_cvge`, `nondecreasing_is_cvge`,
	`nondecreasing_at_right_cvge`, `nondecreasing_at_right_is_cvge`,
	`nonincreasing_at_right_cvge`, `nonincreasing_at_right_is_cvge`
- in `ereal.v`:
  + lemmas `ereal_sup_le`, `ereal_inf_le`

- in `normedtype.v`:
  + definition `lower_semicontinuous`
  + lemma `lower_semicontinuousP`

- in `numfun.v`:
  + lemma `patch_indic`

- in `lebesgue_measure.v`
  + lemma `lower_semicontinuous_measurable`

- in `lebesgue_integral.v`:
  + definition `locally_integrable`
  + lemmas `integrable_locally`, `locally_integrableN`, `locally_integrableD`,
    `locally_integrableB`
  + definition `iavg`
  + lemmas `iavg0`, `iavg_ge0`, `iavg_restrict`, `iavgD`
  + definitions `HL_maximal`
  + lemmas `HL_maximal_ge0`, `HL_maximalT_ge0`,
    `lower_semicontinuous_HL_maximal`, `measurable_HL_maximal`,
    `maximal_inequality`

- in file `measure.v`
  + add lemmas `ae_eq_subset`, `measure_dominates_ae_eq`.

### Changed

- in `normedtype.v`:
  + lemmas `vitali_lemma_finite` and `vitali_lemma_finite_cover` now returns
    duplicate-free lists of indices

- moved from `lebesgue_integral.v` to `measure.v`:
  + definition `ae_eq`
  + lemmas
	`ae_eq0`,
	`ae_eq_comp`,
	`ae_eq_funeposneg`,
	`ae_eq_refl`,
	`ae_eq_trans`,
	`ae_eq_sub`,
	`ae_eq_mul2r`,
	`ae_eq_mul2l`,
	`ae_eq_mul1l`,
	`ae_eq_abse`

### Renamed

- in `exp.v`:
  + `lnX` -> `lnXn`

### Generalized

- in `lebesgue_integral.v`
  + `ge0_integral_bigsetU` generalized from `nat` to `eqType`

### Deprecated

### Removed

### Infrastructure

### Misc
