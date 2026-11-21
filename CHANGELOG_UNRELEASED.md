# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`
  + lemma `in1_mksetP`

- in `topology_structure.v`
  + lemmas `open_bigcup_basis`, `continuous_on_basis`

- in `num_normedtype.v`
  + definition `itvoo_basis`
  + lemma `itvoo_basis_is_basis`

- in `lebesgue_integrable.v`
  + lemma `compact_continuous_Rintegrable`

- in `lebesgue_Rintegral.v`
  + lemmas `Rintegral_gt0`, `Rintegral_gt0_itvcc`

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`

- in `filter.v`:
  + type `filter_display`
  + definition `with_fdisp`
- in `discrete_topology.v`:
  + definition `discrete_display`
- in `function_spaces.v`:
  + definitions `ptws_display`, `arrow_uniform_display`, `uniform_display`, `uniform_fam_display`, `compact_open_display`
- in `initial_topology.v`:
  + definition `initial_display`
- in `one_point_compactification.v`:
  + definition `opc_display`
- in `order_topology.v`:
  + definition `order_display`
- in `quotient_topology.v`:
  + definition `quotient_display`
- in `subspace_topology.v`:
  + definition `subspace_display`
- in `subtype_topology.v`:
  + definition `set_type_topology_def`
- in `sup_topology.v`:
  + definition `supremum_display`
- in `tvs.v`:
  + definition `seminorm_display`

- in `separation_axioms.v`:
  + lemma `separated_set1`

- in `metric_structure.v`:
  + lemma `ball_open`
  + lemma `ball_open_nbhs`
  + lemma `metric_accessible`

- in `realfun.v`:
  + lemma `nondecreasing_discontinuity`

- in `realfun.v`:
  + lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`,
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`,
    `derivable_oo_LRcontinuousS`

- new subdirectory `number_theory`
  + new file `number.v`

- new subdirectory `derive`
  + new files `differential.v`, `derivable.v`, `directional_derive_lemmas.v`, `derive_matrix.v`

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)

- in `filter.v`:
  + implicit arguments of `continuous_comp`

- in `pseudometric_normed_Zmodule.v`:
  + implicit arguments of `distm_lt_split`, `distm_lt_splitr`, `distm_lt_splitl`

- in `pseudometric_structure.v`:
  + implicit arguments of `ball_split`, `ball_splitr`, `ball_splitl`

- moved from `pseudometric_normed_Zmodule.v` to `num_topology.v`
  + lemma `ball_itv`

- moved from `theories` to `number_theory`:
  + files `pi_irrational.v`

- moved from `theories/showcase` to `number_theory`:
  + files `pnt.v`

- the contents of `derive.v` (old) have been transferred to `differential.v`
  (unless stated otherwise)

- moved from `derive.v` (old) to `derivable.v`
  + definitions `derive`, `is_derive`
  + class `is_derive`
  + lemmas `derivable_nbhs`, `derivable_nbhsP`, `derivable_nbhsx`, `derivable_nbhsxP`,
    `derivable0`, `derive0`, `is_derive0`
  + lemma `deriveE`
  + definition `derive1`
  + lemmas `derive1E`, `derive1E'`, `derive1n0`, `derive1n1`, `derive1nS`,
    `derive1Sn`, `derive1Dn`
  + lemmas `deriv1E`, `diff1E`, `derivable1_diffP`, `derivable1P`,
    `diff_derivable`

- moved from `derive.v` (old) to `directional_derive.v`
  + lemma `deriv1E`
  + lemma `derivable_within_continuous `
  + lemma `derivableP`
  + instance `is_derive_cst`
  + lemmas `derivable_cst`, `is_derive_eq`
  + fact `der_add`
  + lemmas `deriveD`, `derivableD`
  + instances `is_deriveD`, `is_derive_sum`
  + lemmas `derivable_sum`, `derive_sum`
  + fact `der_opp`
  + lemmas `deriveN`, `derivableN`
  + instance `is_deriveN`
  + lemmas `deriveB`, `derivableB`
  + fact `der_scal`
  + lemmas `deriveZ`, `derivableZ`
  + instance `is_deriveZ`
  + lemma `derive_cst`
  + lemma `der1_scaleLR`
  + instance `is_derive1ZLR`
  + lemmas `deriveZLR`, `derivableZLR`
  + lemma `derivable_id`
  + instances `is_derive_id`, `is_deriveNid`
  + lemmas `derive_id`, `derive1_one`
  + fact `der_mult`
  + lemmas `deriveM`, `derivableM`, `deriveMr`, `deriveMl`
  + instances `is_deriveM`, `is_deriveX`
  + lemmas `derivableX`, `deriveX`
  + fact `der_inv`
  + lemmas `deriveV`, `derivableV`, `is_deriveV`
  + lemmas `derive_shift`, `derive1_shift`, `is_derive_shift`, `derive_comp_shift`,
    `derive1_comp_shift`, `derivable_comp_shift`, `is_derive_comp_shift`
  + lemmas `derive1_cst`, `derive1Mr`, `derive1Ml`, `exprn_derivable`, `exp_derive`, `exp_derive1`
  + lemmas `compact_EVT_max`, `compact_EVT_min`, `EVT_max`, `EVT_min`, `cvg_at_rightE`,
    `cvg_at_leftE`, `derive1_at_max`, `derive1_at_min`
  + lemmas `Rolle`, `MVT`, `MVT_segment`
  + lemmas `ger0_derive1_lt`, `ger0_derive1_lt_cc`, `ger0_derive1_lt_co`, `ger0_derive1_lt_oc`,
    `ger0_derive1_lt_oo`
  + lemmas `ler0_derive1_lt`, `ler0_derive1_lt_cc`, `ler0_derive1_lt_co`, `ler0_derive1_lt_oc`,
    `ler0_derive1_lt_oo`
  + lemmas `gtr0_derive1_lt`, `gtr0_derive1_lt_cc`, `gtr0_derive1_lt_co`, `gtr0_derive1_lt_oc`,
    `gtr0_derive1_lt_oo`
  + lemmas `ltr0_derive1_lt`, `ltr0_derive1_lt_cc`, `ltr0_derive1_lt_co`, `ltr0_derive1_lt_oc`,
    `ltr0_derive1_lt_oo`
  + lemmas `ler0_derive1_nincry`, `ler0_derive1_nincrNy`, `ger0_derive1_ndecr`,
    `ger0_derive1_ndecry`, `ger0_derive1_ndecrNy`, `decr_derive1_le0`, `decr_derive1_le0_itv`,
    `decr_derive1_le0_itvy`, `decr_derive1_le0_itvNy`, `incr_derive1_ge0`,
    `incr_derive1_ge0_itv`, `incr_derive1_ge0_itvy`, `incr_derive1_ge0_itvNy`, `derive1_comp`
  + instance `is_derive1_comp`
  + lemmas `near_eq_growth_rate`, `near_eq_derivable`, `near_eq_derive`, `near_eq_is_derive`
  + lemmas `near_eq_derive1n_near`, `near_eq_derive1_near`, `near_eq_derive1n`, `near_eq_derive1`
  + fact `der_max_subproof`
  + lemmas `derivable_max`, `derive_maxr`, `derive_maxl`
  + lemmas `derivable_min`, `derive_minr`, `derive_minl`
  + lemma `derive1N`
  + lemma `derivable_opp`
  + lemma `derive1_id`
  + lemma `trigger_derive`
  + lemma `continuous_horner`
  + instance `is_derive_poly`
  + lemma `derivE`
  + lemma `derivable_horner`
  + lemmas `hornerC_ext`, `horner_scale_ext`, `hornerD_ext`, `horner0_ext`
  + lemmas `right_derivative_limit`, `left_derivative_limit`, `derivative_limit`

- moved from `derive.v` (old) to `derive_matrix.v`
  + lemmas `EVT_max_rV`, `EVT_min_rV`
  + definition `jacobian`
  + lemma `deriveEjacobian`
  + lemma `differentiable_coord`
  + lemmas `differentiable_rsubmx`, `differentiable_lsubmx`
  + lemma `derivable_mxP`
  + lemmas `derive_mx`, `is_derive_mx`, `derivable_trmx`, `derive_trmx`
  + instance `is_derive_trmx`
  + lemma `dmx`, `diffmx`
  + instances `is_derive_mx_coord`, `is_derive_mulmx`
  + instance `is_diff_mx`
  + lemmas `derivable_row_mx`, `derive_row_mx`
  + instance `is_derive_row_mx`
  + lemma `eqo_row_mx`
  + lemmas `drow_mx`, `diff_row_mx`, `differentiable_row_mx`
  + instance `is_diff_row_mx`

### Renamed

- in `lebesgue_measure.v`:
  + `compact_finite_measure` -> `compact_lebesgue_measure_lty`

- in `pseudometric_normed_Zmodule.v`:
  + `ball_open` -> `pseudo_ball_open`
  + `ball_open_nbhs` -> `pseudo_ball_open_nbhs`

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

- in `realfun.v`:
  + lemma `nondecreasing_fun_sum_le`

### Removed

- in `derive.v` (old):
  + notation `derivemxE` (deprecated since 1.13.0)

### Infrastructure

### Misc
