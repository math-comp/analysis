# Changelog (unreleased)

## [Unreleased]

### Added

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
  + lemmas `cvg0D`, `cvgD0`, `cvg0B`, `cvgB0`, `cvgN0`

- in `normed_module.v`:
  + lemmas `cvg1M`, `cvgM1`, `cvg0M`, `cvgM0`
  + lemmas `cvg1Z`, `cvg0Z`, `cvgZ0`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_leq`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`,
    `at_left_shift`, `at_right_shift`

- in `num_normedtype.v`,
  + lemmas `pinftyV`, `ninftyV`, `cvgryV`, `cvgrNyV`, `lt0_cvgMlNy`, 
    `lt0_cvgMrNy`, `lt0_cvgMly`, `lt0_cvgMry`

- in `pseudometric_normed_Zmodule.v`,
  + lemmas `fmap_at_left0P`, `fmap_at_right0E`

- in `tvs.v`,
  + lemmas `near_shiftE`, `nearZE`

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
  + lemma `normal_funN`
  + lemma `normal_fun_sym`
  + lemma `normal_fun0abs`
  + lemma `normal_pdf_sym`
  + lemma `normal_fun_center_new`
  + lemma `normal_fun_shift`
  + lemma `normal_pdf_uniq_ae`
  + lemma `normal_prob_continuous`
  + lemma `integral_normal_prob`
  + lemma `measurable_normal_prob`
  + lemma `emeasurable_bounded_integrable`
  + lemmas `integrable_normal_probD1`, `normal_probD1`, `normal_probD2`, `normal_probD`

- in `lebesgue_stieltjes_measure.v`:
  + definition `lebesgue_display`

- in `realsum.v`:
  + lemma `esum_summableP`

- in `esum.v`:
  + lemma `fsetsTE`
- in `ftc.v`:
  + lemma `ge0_integration_by_substitution_shift_itvy`,
    `ge0_integration_by_substitution_shift_itvNy`
- in `derive.v`:
  + lemmas `derivable_row_mx`, `derive_row_mx`
  + instance `is_derive_row_mx`

- in `matrix_normedtype.v`
  + lemmas `norm_row_mx`, `norm_row_mx0r`, `norm_row_mx0l`, `cvg_row_mx`

- in `unstable.v`:
  + lemma `sub_row_mx`

- in `derive.v`:
  + lemmas `eqo_row_mx`, `drow_mx`, `diff_row_mx`,
    `differentiable_row_mx`
  + instance `is_diff_row_mx`

- in `functions.v`:
  + lemmas `zerofctE`, `onefctE`

- in `functions.v`:
  + lemmas `linfunP`, `linfun_eqP`
  + instances of `SubLmodule` and `pointedType` on `{linear _->_ | _ }`

- in `tvs.v`:
  + structure `LinearContinuous`
  + factory `isLinearContinuous`
  + instance of `ChoiceType` on `{linear_continuous _ -> _ }`
  + instance of `LinearContinuous` with the composition of two functions of type `LinearContinuous`
  + instance of `LinearContinuous` with the sum of two functions of type `LinearContinuous`
  + instance of `LinearContinuous` with the scalar multiplication of a function of type
    `LinearContinuous`
  + instance of `Continuous` on \-f when f is of type `LinearContinuous`
  + instance of `SubModClosed` on `{linear_continuous _ -> _}`
  + instance of `SubLModule` on  `{linear_continuous _ -> _ }`
  + instance of `LinearContinuous` on the null function
  + notations `{linear_continuous _ -> _ | _ }` and `{linear_continuous _ -> _ }`
  + definitions `lcfun`, `lcfun_key`, `lcfunP`
  + lemmas `lcfun_eqP`, `null_fun_continuous`, `fun_cvgD`,
   `fun_cvgN`, `fun_cvgZ`, `fun_cvgZr`
  + lemmas `lcfun_continuous` and `lcfun_linear`

- new files `signed_measure.v` and `radon_nikodym.v`
  + with the contents of `charge.v` (deprecated)

- in `esum.v`:
  + lemma `ge0_esum`
  + lemma `esum_ge`

- in `functions.v`:
  + lemma `preimageD1`

- in `measure_function.v`:
  + lemmas `cvg_measure_bigcap`, `cvg_measure_bigcup`

- in `classical_sets.v`:
  + lemma `bigcup_bigsetU`

- in `measurable_structure.v`:
  + lemmas `countable_bigcap_measurable`, `countable_bigcup_measurable`

- in `unstable.v`:
  + definitions `clamp`, `clamp_gele`
  + lemmas `clamp_gemin`, `clamp_lemax`, `minmax_clamp`,
    `clamp_id`, `clamp_min`, `clamp_max`
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in file `nat_topology.v`,
  + new lemma `near_infty_after`.
- in file `num_topology.v`,
  + new lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, `at_right_shift`, `near_right_in_itv`, and `near_left_in_itv`.

- in file `num_normedtype.v`,
  + new lemmas `pinftyV`, `ninftyV`, `cvgryV`, `cvgrNyV`, `lt0_cvgMlNy`, 
    `lt0_cvgMrNy`, `lt0_cvgMly`, and `lt0_cvgMry`.
- in file `pseudometric_normed_Zmodule.v`,
  + new lemmas `fmap_at_left0P`, and `fmap_at_right0E`.
- in file `tvs.v`,
  + new lemmas `near_shiftE`, and `nearZE`.
- in `num_topology.v`:
  + lemmas `near_right_in_itv`, `near_left_in_itv`

### Changed

- in `esum.v`:
  + level of notation `\esum_ ( i 'in' P ) F`
    from level 41 to 34

- in `lebesgue_integral_definition.v`
  + level of notation `\int[ mu ]_( i 'in' D) F`
    from level 36 to 34 and level of `F` from 36 to 41.
    In particular, this means that `\int[mu]_(x in D) f x * g x`
    now parses as `\int[mu]_(x in D) (f x * g x)`.
- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

### Changed

- moved from `tvs.v` to `pseudometric_normed_Zmodule.v`
  + mixin `PreTopologicalNmodule_isTopologicalNmodule`
  + structure `TopologicalNmodule`
  + lemmas `fun_cvgD`, `cvg_sum`, `sum_continuous`
  + mixin `TopologicalNmodule_isTopologicalZmodule`
  + structure `TopologicalZmodule`, type `topologicalZmodType`
  + lemmas `sub_continuous`, `fun_cvgN`
  + factory `PreTopologicalNmodule_isTopologicalZmodule`
  + mixin `PreUniformNmodule_isUniformNmodule`
  + structure `UniformNmodule`
  + mixin `UniformNmodule_isUniformZmodule`
  + structure `UniformZmodule`
  + factory `PreUniformNmodule_isUniformZmodule`
  + lemma `sub_unif_continuous`

- in `tvs.v`:
  + structure `ConvexTvs` now inherits from `UniformZmodule`

- move to `pseudometric_structure.v`:
  + definitions `closed_ball_`, `closed_ball`
  + lemmas `closure_ballE`, `closed_ballxx`, `closed_ball_closed`, `subset_closed_ball`,
    `subset_closure_half`, `le_closed_ball`

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.
- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`

### Renamed

- in `sequences.v`:
  + `limn_einf_shift` -> `limn_einf_addl`
  + `series_le_cvg` -> `series_squeeze_is_cvgn`
- in `pseudometric_normed_Zmodule.v`:
  + `PseudoMetricNormedZmod0` -> `PseudoMetricNormedZmodule`
  + `pseudoMetricNormedZmodType` -> `metricNormedZmodType`
  + `PseudoMetricNormedZmod` -> `MetricNormedZmodule`

- in `normed_module.v`:
  + `PseudoMetricNormedZmod_ConvexTvs_isNormedModule` -> `MetricNormedZmod_ConvexTvs_isNormedModule`

### Generalized

- in `pseudometric_normed_Zmodule.v`:
  + from `pseudoMetricNormedZmodType` to `PseudoMetricNormedZmod0.type`:
    * lemma `le0_ball0`
    * lemma `cvg_bounded`
    * lemma `bounded_cst`
  + from `realFieldType` to `numFieldType`
    * lemma `bounded_funN`
    * lemma `bounded_funD`

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvgD`, `cvg0D`, `cvgD0`, `cvgN`, `cvgNP`, `cvgB`, `cvg0B`, `cvgB0`, `cvgN0`,
    `cvg_sub0`, `cvg0`, `subr_cvg0`
  + lemmas `within_continuousD`, `within_continuousB`, `within_continuousN`
  + lemmas `le_closed_ball`, `closed_ball0`
- in `tvs.v`:
  + lemma `nbhsB`

### Deprecated

- in `pseudometric_normed_Zmodule.v`:
  + lemma `fun_cvgD` (use `cvgD` instead)
  + lemma `fun_cvgN` (use `cvgN` instead)

### Removed

- in `tvs.v`:
  + structure `PreUniformLmodule`
  + mixin `PreUniformLmodule_isUniformLmodule`
  + structure `UniformLmodule`
  + factory `UniformNmodule_isUniformLmodule`
  + lemma `prod_add_continuous` (remains accessible via the generic `add_continuous` of `TopologicalNmodule.type`)

- in `pseudometric_normred_Zmodule.v`:
  + lemma `pseudoMetricNormedZModType_hausdorff` (deprecated since 1.10.0)

### Infrastructure

### Misc
