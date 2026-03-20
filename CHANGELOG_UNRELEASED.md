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
- in `ereal_normedtype.v`:
  + lemma `ge0_cvgMly`
- in `unstable.v`:
  + lemma `itv_boundlr_lt`,
  + module `EndlessDense`
    * definitions `is_endless`, `is_dense`
    * lemmas `itv_bound_half_dense`
    * defintions `dual_itv_bound`, `dual_itv`
    * lemmas `dual_itvE`, `dual_itv_sub_memP`, `dual_is_dense`, `dual_is_endless`,
      ` dual_itv_boundK`, `dual_itv_bound_lt`, `dual_itv_bound_le`
    * lemmas `subitvP`, `numDomain_is_endless`, `numField_is_dense`
  + lemma `real_subitvP`

- in `classical_sets.v`:
  + lemma `powerset0`, `powerset1`, `powerset2`, `powersetS`,
    `setorder_itv_setUl_image`, `setorder_itv_setUr_image`,
    `setorder_itv_setDl_image`

- in set_interval.v
  + lemmas `itv_open_endsPn`, `itv_closed_endsPn`, `itv_open_ends_boundlr`

- in topology_structure.v
  + lemmas `closureEbigcap_itvcy`,`interiorEbigcup_itvNyc`,
    `closureEbigcap_itvcc`,`interiorEbigcup_itvcc`

- in num_topology.v
  + module `EndlessDenseTopology` (internal)
  + lemmas `open_itv_open_ends`, `closed_itv_closed_ends`,
    `itv_closureE`, `itv_interiorE`

- in `sequences.v`:
  + lemma `sdrop_shift`
  + lemma `ge_einfs`
  + lemma `einfs_shift`
  + lemma `limn_einf_shift_new`
  + lemma `limn_einf_shiftS`
  + lemma `limn_einf_cst`
- in `uniform_structure.v`:
  + lemma `unif_continuous_continuous`
- in `uniform_structure.v`:
  + lemma `unif_continuous_comp`

- in `initial_topology.v`:
  + lemma `initial_unif_continuous`
  + lemma `initial_unif_continuous_comp`
  + lemma `initial_unif_continuous_comp_fst`
  + lemma `initial_unif_continuous_comp_snd`
  + lemma `initial_nbhs_preimage`

- in `product_topology.v`:
  + lemma `entourage_prod_exS`
  + definition `interchange_prod`
  + lemma `entourage_interchange_prod`
  + lemma `pair_unif_continuous`
  + lemma `fst_unif_continuous`
  + lemma `snd_unif_continuous`

- in `metric_space.v`:
  + definition `prod_mdist`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `PseudoMetricNormedZmodule_add_unif_continuous`
  + lemma `PseudoMetricNormedZmodule_opp_unif_continuous`
  + lemma `standard_scale_continuous`
  + notation `topologicalNmodType`

- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

- in `num_normedtype.v`,
  + lemmas `pinftyV`, `ninftyV`, `cvgryV`, `cvgrNyV`, `lt0_cvgMlNy`, 
    `lt0_cvgMrNy`, `lt0_cvgMly`, `lt0_cvgMry`

- in `pseudometric_normed_Zmodule.v`,
  + lemmas `fmap_at_left0P`, `fmap_at_right0E`

- in `unstable.v`:
  + definitions `clamp`, `clamp_gele`
  + lemmas `clamp_gemin`, `clamp_lemax`, `minmax_clamp`,
    `clamp_id`, `clamp_min`, `clamp_max`
  + lemma `seminorm_normrB`

- in `topology_structure.v`:
  + lemma `id_continuous`
  + definition `nbhs_basis`
  + definition `openU_from`

- in `normed_module.v`:
  + lemma `ball_convex_set` (was a `Let`)

- in `classical_sets.v`:
  + notation ``... `+ ...``
  + lemmas `addsetS`, `add0set`, `addsetI`, `addsetA`

- in `convex.v`:
  + lemmas `lt_conv`, `le_conv`
  + lemma `convD`

- in `pseudmetric_normed_Zmodule.v`:
  + lemma `continuous_shift`
  + lemma `nbhs_add1set`

- in `tvs.v`:
  + definition `balanced_set`
  + definition `absolutely_convex_set`
  + lemma `absolutely_convex0`
  + definition `absorbing_set`
  + lemma `absolutely_convex_setX`
  + definition `init_subconvextvs`
  + factory `NbhsBasisAt0_isConvexTvs`
  + definition `filter_from_basis0`
  + factory `NbhsSubbasisAt0_isConvexTvs`
  + definition `finI_fromsubbasis0`
  + lemma `openD`
  + lemma `openB`
  + lemma `nbhsE0`
  + lemma `openZ`
  + lemma `continuousZl`
  + lemma `continuousZr`
  + lemma `scalerx_continuous`
  + lemma `scalexr_continuous`
  + definition `nbhsbasis_convextvs`
  + definition `open_nbhsbasis_convextvs`
  + definition `open_absconvex_opennbhsbasis`
  + definition `basis_opennbhsbasis`
  + lemma `basis_neqset0`
  + lemma `absorbing_opennbhsbasis`
  + definition `gauge_fun`
  + definition `seminorm_on`
  + definition `seminorm_subbasis`
  + lemmas `nonempty_subbasis`, `mem0_seminorm_subbasis`, `split_seminorm_subbasis`,
    `expand_seminorm_subbasis`
  + lemmas `convex_seminorm_subbasis`, `balanced_seminorm_subbasis`,
    `absolutely_convex_seminorm_subbasis`, `absorbing_seminorm`, `continuous_at0_seminorm`,
    `continuous_seminorm`
  + definitions `gauge_fun_basis`, `seminorm_of`
  + theorem `seminorm_convextvs`
  + lemma `continuous_seminorm_of`
  + lemma `linear_continuous_seminorm`
  + lemma `linear_seminorm_continuous`
  + proposition `lcfun_seminorm`

- in `hahn_banach_theorem.v`
  + theorem `hahn_banach_extension_subctvs`
  + theorem `hahn_banach_extension_initialsubctvs`

- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

- new file `edist.v`
- in `classical_sets.v`
  + lemma `bigcup_idset1`

- in `esum.v`:
  + lemma `nonempty_esumy`
  + lemma `infinite_esum_cst`

- in `random_variable.v`:
  + lemma `not_range_pmf0`
  + lemma `dRV_esum_pmf_distribution`

- in `measure_theory/measure_function.v`:
  + lemma `semi_cvg_measure_bigcap`
- in `num_normedtype.v`:
  + `continuous_within_itvbbP`,
    `continuous_within_itvocP`, `continuous_within_itvcoP`,
    `continuous_within_itvbyP`, `continuous_within_itvNybP`
- in `num_topology.v`:
  + lemma `not_nearP`
  + lemma `not_nearPball`
- in `pseudometric_structure.v`:
  + lemma `cvg_withinP`

- in `ftc.v`:
  + lemma `integration_by_partsy_ge0_ge0`
  + lemma `integration_by_partsy_le0_ge0`
  + lemma `integration_by_partsy_le0_le0`
  + lemma `integration_by_partsy_ge0_le0`

- in `realfun.v`:
  + lemma `derivable_oy_RcontinuousN`
  
- in `topology_structure.v`:
  + definitions `separable_set`, `separable`
  + lemmas `basisP`, `separableTE`, `second_countable_separable`,
    `bigcupT_separable`, `bigcup_separable`
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in file `nat_topology.v`,
  + new lemma `near_infty_after`.
- in file `num_topology.v`,
  + new lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, `at_right_shift`, `near_right_in_itv`, and `near_left_in_itv`.
- in file `nat_topology.v`:
  + lemma `near_infty_after`

- in file `realfun.v`:
  + new lemmas `lhopital_at_pinfty`, `lhopital_at_ninfty`, `lhopital_Ninfty_at_right`, `lhopital_ninfty_at_right`, `lhopital_Ninfty_at_left`, `lhopital_pinfty_at_left`, `lhopital_ninfty_at_left`, `lhopital_Ninfty`, `lhopital_pinfty`, `lhopital_ninfty`, `lhopital_Ninfty_at_pinfty`,  `lhopital_ninfty_at_pinfty`, `lhopital_Ninfty_at_ninfty`,  `lhopital_pinfty_at_ninfty`, `lhopital_ninfty_at_ninfty`.
- in `realfun.v`:
  + lemmas `lhopital_at_pinfty`, `lhopital_at_ninfty`,
    `lhopital_Ninfty_at_right`, `lhopital_pinfty_at_right`, `lhopital_ninfty_at_right`,
    `lhopital_Ninfty_at_left`, `lhopital_pinfty_at_left`, `lhopital_ninfty_at_left`,
    `lhopital_Ninfty`, `lhopital_pinfty`, `lhopital_ninfty`,
    `lhopital_Ninfty_at_pinfty`, `lhopital_pinfty_at_pinfty`, `lhopital_ninfty_at_pinfty`,
    `lhopital_Ninfty_at_ninfty`, `lhopital_pinfty_at_ninfty`, `lhopital_ninfty_at_ninfty`
- in `lebesgue_Rintegral.v`:
  + definition `measure_of_density`
  + lemmas `integral_measure_of_density_indic`,
    `integral_measure_of_densityMindic`, `sintegral_measure_of_density`,
    `integral_measure_of_density`

- new file `counting_lebesgue.v`:
  + lemmas `cstMcounting_esum`, `sintegral_counting_esum`,
    `integral_countingT_esum`, `integral_counting_esum`

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

- in `cardinality.v`:
  + `sub_finite_set` (order of parameters)

- in `normed_module.v`:
  + `segment_compact` is now a hint

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
