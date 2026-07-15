# Changelog (unreleased)

## [Unreleased]

### Added

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvg0D`, `cvgD0`, `cvg0B`, `cvgB0`, `cvgN0`

- in `normed_module.v`:
  + lemmas `cvg1M`, `cvgM1`, `cvg0M`, `cvgM0`
  + lemmas `cvg1Z`, `cvg0Z`, `cvgZ0`

- in `normed_module.v`:
  + structure `NormedVector`
  + notation `normedVectType`
  + definition `max_space`
  + lemmas `sup_closed_ball_compact`, `equivalence_norms`,
    `linear_findim_continuous`

- in `tvs.v`:
  + lemmas `cvg_sum`, `sum_continuous`

- in `classical_sets.v`:
  + lemmas `setI_closed_setT`, `setI_closed_set0`

- in `measurable_function.v`:
  + lemma `g_sigma_algebra_preimage_comp`

- in `measure_function.v`:
  + lemma `g_sigma_algebra_finite_measure_unique`

- new file `independence.v`:
  + definition `independent_events`
  + definition `mutual_independence`
  + lemma `eq_mutual_independence`
  + definition `independence2`, `independence2P`
  + lemma `mutual_independence_fset`
  + lemma `mutual_independence_finiteS`
  + theorem `mutual_independence_finite_g_sigma`
  + lemma `mutual_dependence_bigcup`
  + definition `independent_RVs`
  + lemma `independent_RVsD1`
  + theorem `independent_generators`
  + definition `independent_RVs2`
  + lemmas `independent_RVs2_comp`, `independent_RVs2_funrposneg`,
    `independent_RVs2_funrnegpos`, `independent_RVs2_funrnegneg`,
    `independent_RVs2_funrpospos`
  + definition `pairRV`, lemma `measurable_pairRV`
  + lemmas `independent_RVs2_product_measure1`
  + lemmas `independent_RVs2_setI_preimage`,
    `independent_Lfun1_expectation_product_measure_lty`
  + lemma `ge0_independent_expectationM`
  + lemmas `independent_Lfun1_expectationM_lty`, `independent_Lfun1M`,
    `independent_expectationM`

- in `ereal.v`:
  + lemma `ge0_addBefctE`

- in `measure_extension.v`:
  + definition `caratheodory_measure`
- in `measurable_structure.v`:
  + structure `PMeasurable`, notation `pmeasurableType`

- in `subspace_topology.v`:
  + lemma `withinU_continuous_patch`
- in `matrix_normedtype.v`:
  + lemma `continuous_mx`

- in `derive.v`:
  + instance `is_derive_mx`
  + fact `dmx`
  + lemma `diffmx`
  + lemma `is_diff_mx`
  + instance `is_diff_mx`
- in `realsum.v`:
  + lemma `esum_psum`
  + lemma `esum_sum`

- in `constructive_ereal.v`:
  + definition `esg`
  + lemmas `numEesg`, `gte0_esg`, `lte0_esg`, `esg0`

- in `esum.v`:
  + lemmas `esum_eq0P`, `esumZ`, `exchange_esum`
  + lemmas `le_esum`, `esumN`
  + lemmas `summable_le_esum`, `summable_esum_funepos`, `summable_esumN`,
    `summableZ`, `summable_esumZ`
  + lemmas `esum_if_eq_op`
  + lemmas `exchange_esum_ereal_sup`

- in `ereal.v`:
  + lemmas `exchange_ereal_sup`, `ge0_ereal_supZl`, `ge0_ereal_supZl_range`

- in `sequences.v`:
  + lemmas `ereal_supD`, `ereal_sup_sum`

- in `reals.v`:
  + lemmas `sup_ge0`, `has_sup_wpZl`, `gt0_has_supZl`, `has_sup_Mn`, `sup_Mn`
- in `mathcomp_extra.v`:
  + lemmas `divDl_ge0`, `divDl_le1`

- in `unstable.v`:
  + lemmas `divD_onem`

- in `filter.v`:
  + mixin `isSubNbhs`, structure `SubNbhs`, notation `subNbhsType`
  + new lemmas `near_eq_cvgE`, `near_eq_is_cvg`, `near_eq_lim`, 
    `cvg_to_eq`, `cvg_to_withinP`, and `within_cvg_to_within`.

- in `topology_structure.v`:
  + structure `SubTopological`, notation `subTopologicalType`

- in `tvs.v`:
  + structure `SubConvexTvs`, notation `subConvexTvsType`

- in `normed_module.v`:
  + structure `SubNormedModule`, notation `subNormedModType`
  + instance `ent_xsection_filter`
  + light-weigth factory `subLmodule_isSubNormedmodule`

- new file `hahn_banach_theorem.v`:
  + module `LinearGraph`
    * definitions `graph`, `linear_graph`
    * lemmas `lingraph_00`, `lingraphZ`, `lingraphD`
  + module `HahnBanachZorn`
    * definitions `extend_graph`, `le_graph`, `functional_graph`, `le_extend_graph`
    * record `zorn_type`
    * definition `zphi`
    * lemma `zorn_type_eq`
    * definition `zornS`
    * lemmas `zornS_ex`, `domain_extend`, `hahn_banach_witness`
  + theorems `hahn_banach_extension`, `hahn_banach_extension_normed`
- in `normal_distribution.v`:
  + definition `post_stddev`
  + lemmas `post_stddev_gt0`, `post_stddevE`
  + definition `post_mean`
  + lemmas `normal_fun_conjugate`, `normal_pdf_conjugate`, `normal_prob_conjugate`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_leq`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`,
    `at_left_shift`, `at_right_shift`
- in `esum.v`:
  + lemmas `pos_esum_ge1`, `le_pos_esum_fine`, `sum_esum_ge`, `le_esum_fine`,
    `subset_esum`, `esum0`, `esum_if_eq_op_set1`, `esum_neq0`, `esum_ge1`
  + lemmas `eq_esummable`, `le_esummable`, `esummableZl`, `esummableZr`,
    `esummableMl`, `esummableMr`, `esummableM`
  + lemmas `esummable_esum_funepos`, `esummable_esum_funeneg`,
     `esummable_esum_fin_num`, `esummable_esumN`
  + lemma `esumE`
  + lemmas `esummable_esumZ`, `esummable_esumD`, `esummableB`

- new files (result of the splitting of `trigo.v`):
  + `elementary_functions/trigo.v`
  + `elementary_functions/trigonometry_functions.v`
  + `elementary_functions/trigonometry_integral.v`

- in `topology_structure.v`:
  + lemma `id_continuous`
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in file `nat_topology.v`,
  + new lemma `near_infty_after`.
- in file `num_topology.v`,
  + new lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, and `at_right_shift`.

- in file `normed_module.v`,
  + new lemmas `cvg1MC`, `cvg1M`, `cvgCM1`, `cvgM1`, `cvg0MC`, `cvg0M`, 
    `cvgCM0`, and `cvgM0`.
- in file `pseudometric_normed_Zmodule.v`,
  + new lemmas `cvgDl`, `cvgDr`, `cvgBl`, `cvgBr`, `cvg0D`, `cvg0DC`, 
    `cvgD0`, `cvgCD0`, `cvg0B`, `cvg0BC`, `cvgB0`, `cvgCB0`, and `cvgN0`.

- in `derive.v`
  + new lemmas `derive1Dn`, `der1_scaleLR`, `deriveZLR`, `derivableZLR`, 
    `derivable_shiftf`, `derive_shiftf`, `is_derive_shiftf`, `derive1_shiftf`, 
    `near_eq_derive1n_near`, `near_eq_derive1_near`, `near_eq_derive1n`, and 
    `near_eq_derive1`.

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

- moved from `trigo.v` to `trigonometry_integral.v`:
  + lemmas `integral0_oneDsqr`, `integral0y_oneDsqr`

- moved from `trigo.v` to `trigonometry_functions.v`:
  + all contents except lemmas `integral0_oneDsqr`, `integral0y_oneDsqr`

- moved from `realfun.v` to `derive.v`: 
  + lemmas `is_deriveV`, `is_derive1_comp`.

### Renamed

- in `esum.v`:
  + `summable` -> `esummable`
  + `summable_pinfty` -> `esummable_pinfty`
  + `summableE` -> `esummableE`
  + `summableD` -> `esummableD`
  + `summableN` -> `esummableN`
  + `summableB` -> `esummableB`
  + `summable_funepos` -> `esummable_funepos`
  + `summable_funeneg` -> `esummable_funeneg`
  + `summable_fine_sum` -> `esummable_fine_sum`
  + `summable_cvg` -> `esummable_cvg`
  + `summable_nneseries_lim` -> `esummable_nneseries_lim`
  + `summable_eseries` -> `esummable_eseries`
  + `summable_eseries_esum` -> `esummable_eseries_esum`

- in `lebesgue_integrable.v`:
  + `integrable_summable` -> `integrable_esummable`

- in `lebesgue_integral_nonneg.v`:
  + `summable_integral_dirac` -> `esummable_integral_dirac`
- `mathcomp_extra.v` -> `mathcomp_compat.v`

### Generalized

- in `esum.v`:
  + lemmma `le_esum`

- from `pseudometric_normed_Zmodule.v` to `topology_structure.v`:
  + lemma `continuous_comp_cvg`

### Deprecated

### Removed

- in `unstable.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq` (now in MathComp 2.6.0)

- in `classical_sets.v`:
  + notations `preimage_itv_o_infty`, `preimage_itv_c_infty`,
    `preimage_itv_infty_o`, `preimage_itv_infty_c`
    (deprecated since 1.8.0)

- in `constructive_ereal.v`:
  + notations `maxeMr`, `maxeMl`, `mineMr`, `mineMl`
    (deprecated since 1.8.0)

- in `derive.v`:
  + notation `le0r_derive1_ndecr` (deprecated since 1.9.0)

- in `set_interval.v`:
  + notations `opp_itv_bnd_infty`, `opp_itv_infty_bnd` (deprecated since 1.9.0)

- in `Rstruct.v`:
  + definition `Rinvx` (deprecated since 1.9.0)

- in `real_interval.v`:
  + notations `itv_bnd_infty_bigcup`, `itv_bnd_infty_bigcup0S`, `itv_infty_bnd_bigcup`
    (deprecated since 1.9.0)

- in `num_topology.v`:
  + notations `nbhs_lt`, `nbhs_le` (deprecated since 1.9.0)

- in `normed_module.v`:
  + notation `cvge_sub0` (deprecated since 1.9.0)

- in `num_normedtype.v`:
  + notation `cvgyNP` (deprecated since 1.9.0)

- in `measurable_function.v`:
  + notation `preimage_class_measurable_fun` (deprecated since 1.9.0)

- in `measurable_structure.v`:
  + notations `setDI_closed`, `setDI_semi_setD_closed`, `sedDI_closedP`,
    `setringDI`, `preimage_classes`, `preimage_classes_comp`
    (deprecated since 1.9.0)

### Infrastructure

### Misc
