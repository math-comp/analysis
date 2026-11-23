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

- new subdirectory `number_theory`
  + new file `number.v`

- new file `sub_pmf.v`:
  + definition `discrete_measurable_space`
  + mixin `isSubPmf`, factory `uniq_isSubPmf`, structure `SubPmf`,
    notation `R.-pmf T`
  + definition `sub_pmf`, lemma `sub_pmfP`
  + definition `measure_of_pmf`
  + definition `dinsupp`, abbreviation `dweight`
  + definitions `pmf_prob`, `pmf_cprob`, `pmf_expectation`,
    `pmf_cexpectation`, notations `\P_[mu] E`, `\P_[mu, A] E`,
    `\E_[mu] f`, `\E_[mu, A] f`
  + definition `pmf_esummable`
  + definitions `pmf_zero`, `pmf_restr`, `pmf_count`, `pmf_ret`,
    `pmf_uniform`, `pmf_flip`
  + definition `pmf_bind`, notation `\bind_(i <- d) E`,
    definitions `pmf_bindr`, `pmf_iter`
  + definition `pmf_lim`, notation `\lim_(n) E`
  + definition `pmf_margin`, abbreviations `pmf1`, `pmf2`,
    definition `pmf_swap`
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

### Moved

- from `pseudometric_normed_Zmodule.v` to `num_topology.v`
  + lemma `ball_itv`

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
  + lemma `measure_of_pmf_zero`
  + definition `pmf_restr`
  + lemma `measure_of_pmf_restr`
  + lemmas `esum_pmf_setT`, `esum_pmf_range1`, `esum_pmf_pred`
  + lemma `pmf_prob_dRV`
  + lemmas `pmf_restrD`, `supp_pmf_restr`
  + definition `pmf_count`
  + lemmas `pmf_count_ge0`, `pmf_count_sum_le1`, `pmf_count_sum_eq1`,
    `esummable_pmf_count`
  + definition `pmf_ret`
  + lemmas `pmf_retE`, `pmf_retxx`, `pmf_ret0`, `in_pmf_ret`, `measure_of_pmf_ret`
  + definition `pmf_uniform`
  + lemma `pmf_uniformE`
  + definition `pmf_flip`
  + definition `pmf_bind`, notation `\bind_(i <- d) E`,
  + lemmas `pmf_bind_zero`, `pmf_ret_bind`, `pmf_bind_ret`
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

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in `nat_topology.v`:
  + new lemma `near_infty_after`.
- in `num_topology.v`;
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, `at_right_shift`
- in `realfun.v`:
  + lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`, 
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`,
    `derivable_oo_LRcontinuousS`

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

### Infrastructure

### Misc
