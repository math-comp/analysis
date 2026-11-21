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

- in `unstable.v`:
  + definition `supp`
  + lemmas `mem_supp`, `mem_suppP`, `memNsuppP`

- in `sequences.v`:
  + lemma `ereal_nondecreasing_sum_limn`

- new file `sub_pmf.v`:
  + definition `discrete_measurable_space`
  + lemma `esum_setT_discrete`
  + lemmas `measurable_discrete`, `measurable_fun_discrete`
  + lemma `measurable_fun_discreteT`
  + mixin `isSubPmf`, structure `SubPmf`, notation `R.-pmf T`
  + definition `measure_of_pmf`
  + lemma `integral_measure_of_pmf`
  + lemma `esummable_integrable`
  + lemma `expectation_pmf`, `expectation_pmfEFin`
  + lemma `expectation_pmf0`
  + factory `uniq_isSubPmf`
  + lemma `subpmf_le1`
  + definitions `pmf_prob`, `pmf_cprob`, `pmf_expectation`,
    `pmf_cexpectation`, notations `\P_[mu] E`, `\P_[mu, A] E`,
    `\E_[mu] f`, `\E_[mu, A] f`
  + definition `pmf_esummable`
  + abbreviation `dweight`
  + definition `subpmf_sum`, lemma `subpmf_sumP`
  + definition `pmf_zero`
  + lemma `pmf_zeroE`, `measure_of_pmf_zero`
  + definition `pmf_restr`
  + lemma `measure_of_pmf_restr`
  + lemmas `esum_pmf_setT`, `esum_pmf_range1`, `esum_pmf_pred`
  + lemma `pmf_prob_dRV`
  + lemmas `pmf_restrD`, `supp_pmf_restr`
  + definition `pmf_count`
  + lemmas `pmf_countE`, `pmf_count_sum_eq1`, `esummable_pmf_count`
  + definition `pmf_ret`
  + lemmas `pmf_retE`, `pmf_retxx`, `pmf_ret0`, `in_pmf_ret`, `measure_of_pmf_ret`
  + definition `pmf_uniform`
  + lemma `pmf_uniformE`
  + definition `pmf_flip`, lemma `pmf_flipE`
  + definition `pmf_bind`, notation `\bind_(i <- d) E`,
  + lemmas `pmf_bindE`, `pmf_bind_zero`, `pmf_ret_bind`, `pmf_bind_ret`
  + lemma `supp_eq_pmf_bind`
  + lemma `esummable_pmf_bind_elt`
  + lemma `pmf_bind_is_fin_num`
  + lemma `EFin_pmf_bind`
  + lemma `supp_le_pmf_bind`
  + lemma `le_pmf_bind`
  + lemma `supp_le_pmf_bind2`
  + lemma `pmf_bindC`
  + lemma `supp_pmf_bind`
  + lemma `pmf_bind_mem_supp`
  + lemmas `pmf_bind_eq0`, `eq0_pmf_bind`
  + definitions `pmf_bindr`, `pmf_iter`
  + lemma `measure_of_pmf_bind`
  + lemma `measurable_measure_of_pmf`
  + lemma `measure_of_pmf_bind_giry`
  + lemma `pmf_bind_pmf_bind`
  + lemma `pmf_bind_additive`
  + definition `pmf_lim`, notation `\lim_(n) E`
  + lemma `EFin_pmf_lim`
  + lemma `pmf_limE`
  + lemma `EFin_pmf_lim_limn`
  + lemma `EFin_pmf_lim_sup`
  + lemmas `pmf_limC`, `pmf_lim_bump`, `pmf_lim_lift`, `pmf_lim_ge0`, `pmf_lim_le1`,
    `le_pmf_lim`, `eq_pmf_lim`
  + lemmas `leub_pmf_lim`, `pmf_lim_ub`
  + lemmas `pmf_limM_sup`, `pmf_bind_lim`, `pmf_lim_bind`
  + lemmas `leub_pmf_lim_pmf_lim1`, `pmf_lim_pmf_lim_ub1`, `leub_pmf_lim_pmf_lim2`,
    `pmf_lim_pmf_lim_ub2`, `pmf_lim_pmf_lim`
  + lemma `nondecreasing_pmf_bind`
  + lemma `pmf_bind_pmf_lim_diag`
  + definition `pmf_margin`
  + lemmas `pmf_marginE`, `pmf_bind_margin`, `pmf_margin_bind`,
    `pmf_margin_ret`
  + lemma `measure_of_pmf_margin`
  + abbreviations `pmf1`, `pmf2`
  + definition `pmf_swap`
  + lemmas `pmf_swapE`, `pmf_swapK`, `supp_pmf_swap`, `pmf1_swap`,
    `pmf2_swap`
  + lemmas `pmf1E`, `esummable_fst`
  + lemmas `pmf2E`, `esummable_snd`
  + lemmas `pmf_esummable_cst`, `pmf_esummableZ`, `bounded_pmf_esummable`,
    `esummable_pmf`
  + lemmas `pmf_expectationZ`, `pmf_expectation_cst`, `pmf_expectation0`,
    `supp_eq_pmf_expectation`, `pmf_expectationE`, `pmf_expectationB`,
    `pmf_expectation_ge0`
  + lemmas `expectation_pmf_ret`, `expectation_pmf_zero`, `expectation_pmf_bind`,
    `expectation_pmf_margin`, `expectation_pmf_bind_EFin`
  + lemmas `measure_of_pmf_distribution`, `ge0_expectation_pmf`,
    `expectation_pmf_integral`, `expectation_pmf_expectation`
  + lemmas `prE`, `prE_measure`, `pmf_prob_pred0`, `pmf_prob_pred1`,
    `pmf_prob_expectation`, `pmf_prob_predT`, `expectation_pmf_cst`
  + lemmas `pmf_expectation_ret`, `pmf_expectation_zero`, `dweight_pmf_zero`,
    `pmf_expectation_margin`, `pmf_prob_ge0`, `pmf_cprob_ge0`, `supp_eq_pmf_prob`,
    `eq_pmf_prob`, `pred0_pmf_prob_eq0`
  + lemmas `pmf_prob_eq0`, `eq0_pmf_cprob`, `subset_pmf_prob`, `pmf_prob_le1`,
    `pmf_prob_bind`, `pmf_prob_margin`, `pmf_expectation_le`
  + lemmas `le_mem_pmf_prob`, `le_pmf_pmf_prob`, `pmf_cprob_le1`, `pmf_cprob_sum`,
    `eq0_pmf_prob`, `pmf_probID`, `pmf_prob_predU_indep`
  + lemmas `pmf_prob_mem_map`, `pmf_prob_mem_map`, `pmf_prob_mem`,
    `pmf_prob_bigor_indep`, `pmf_prob_predU`, `pmf_prob_predI`,
    `le_pmf_prob_predU`, `le_pmf_prob_predI`, `pmf_prob_predC`,
    `pmf_prob_split`, `pmf_cprob_pred1`
  + lemmas `esummable_pmf_prob_f`, `esum_is_fin_num_mu_f`,
    `pmf_prob_cexpectation_esum`, `pmf_expectation_split`,
    `bounded_pmf_expectation_le`, `ge0_pmf_expectation_bind`,
    `le_pmf_esummable`, `pmf_esummable_expectation`,
    `pmf_expectation_bind`
  + lemmas `nondecreasing_esum_Efn`, `esum_pmf_lim_r`, `esum_pmf_lim_r_r`, `esum_pmf_lim`
  + lemma `pmf_lim_limn`
- new subdirectory `derive`
  + new files `differential.v`, `directional_derive.v`, `derive_matrix.v`

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

- in `cardinality.v`:
  + `sub_finite_set` (order of parameters)

- in `normed_module.v`:
  + `segment_compact` is now a hint
- the contents of `derive.v` (old) have been transferred to `differential.v`
  (unless stated otherwise)

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

- in `lebesgue_integrable.v`:
  + `integrable_esummable` -> `integrable_bigcup_esummable_integral`

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

- in `hoelder.v`:
  + `finite_form` (from `R` to `\bar R`)

- in `random_variable.v`:
  + `expectation` (from `R` to `\bar R`)

- in `constructive_ereal.v`:
  + lemma `fineM`

### Deprecated

- in `realfun.v`:
  + lemma `nondecreasing_fun_sum_le`

### Removed

- in `derive.v` (old):
  + notation `derivemxE` (deprecated since 1.13.0)

### Infrastructure

### Misc
