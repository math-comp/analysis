# Changelog (unreleased)

## [Unreleased]

### Added

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

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in file `nat_topology.v`,
  + new lemma `near_infty_after`.
- in file `num_topology.v`,
  + new lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, and `at_right_shift`.
- in `realfun.v`:
  + lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`, 
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`,
    `derivable_oo_LRcontinuousS`

### Changed

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
