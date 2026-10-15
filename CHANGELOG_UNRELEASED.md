# Changelog (unreleased)

## [Unreleased]

### Added

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

- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

- new file `edist.v`

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
  + lemmas `lhopital_pinfty_at_right`, `lhopital_pinfty_at_pinfty`

### Changed

- in `esum.v`:
  + level of notation `\esum_ ( i 'in' P ) F`
    from level 41 to 34

- in `lebesgue_integral_definition.v`
  + level of notation `\int[ mu ]_( i 'in' D) F`
    from level 36 to 34 and level of `F` from 36 to 41.
    In particular, this means that `\int[mu]_(x in D) f x * g x`
    now parses as `\int[mu]_(x in D) (f x * g x)`.

- moved from `tvs.v` to `pseudometric_normed_Zmodule.v`:
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

- in `topology/topology_structure.v`:
  + lemma `bigcap_open`
- moved to `ereal.v` from `ereal_normedtype.v`:
  + lemma `nbhs_EFin`

- moved to `ereal.v` from `normed_module.v`:
  + lemma `fcvg_is_fine`
  + lemma `fine_fcvg`
  + lemma `cvg_EFin`
  + lemma `fine_cvg`
  + lemma `cvg_is_fine`
  + lemma `fine_cvgP`

- moved to `edist.v` from `urysohn.v`:
  + definitions `edist`, `edist_inf`
  + lemmas `edist_ge0`, `edist_neqNy`, `edist_lt_ball`, `edist_fin`,
    `edist_pinftyP`, `edist_finP`, `edist_fin_open`, `edist_fin_closed`,
    `edist_pinfty_open`, `edist_sym`, `edist_triangle`, `edist_continuous`,
    `edist_closeP`, `edist_refl`, `edist_closel`
  + lemmas `edist_inf_ge0`, `edist_inf_neqNy`, `edist_inf_triangle`,
    `edist_inf_continuous`, `edist_inf0`
- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`

- moved from `tvs.v` to `pseudometric_normed_Zmodule.v`
  and generalized:
  + lemma `nbhsB_subproof`, `nbhsT_subproof`
  + lemma `nbhsB`

- moved from `pseudometric_normed_Zmodule.v` to `num_normedtype.v`:
  + lemmas `continuous_within_itvP`, `continuous_within_itvcyP`, `continuous_within_itvNycP`, `within_continuous_continuous`
- moved from `pseudometric_normed_Zmodule.v` to `num_topology.v`:
  + lemmas `cvg_at_right_filter`,
    `cvg_at_left_filter`, `cvg_at_right_within`, `cvg_at_left_within`

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

- in `pseudometric_normed_Zmodule.v`:
  + `continuous_within_itvP` -> `continuous_within_itvccP`

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
  + lemmas `fun_cvgZ`, `fun_cvgZr`
  + lemmas `nbhsZ`, `nbhs0Z`

- in `esum.v`:
  + lemmas `esum_bigcupT`, `esum_bigcup`

- in `metric_structure.v`:
  + lemmas `metric_sym`, `mdistxx`, `mdist_gt0`
  + lemmas `metric_triangle`, `metric_hausdorff`
- in `measure_theory/measure_function.v`:
  + lemma `cvg_measure_bigcap`

- in `numfun.v`:
  + lemma `itv_partition_nth_ge`
- in `num_normedtype.v`:
    `continuous_within_itvcyP`,
    `continuous_within_itvNycP`, `continuous_within_itvP`,
    `within_continuous_continuous` generalized from `pseudoMetricNormedZmodType` to `pseudoMetricType`
- in `pseudometric_structure.v`:
  + lemma `cvg_nbhsP` generalized from `metricType` to `pseudoMetricType`
- in `realfun.v`:
  + lemmas `cvg_at_rightP`, `cvg_at_leftP`, `cvgr_dnbhsP`, `cvge_at_rightP`, `cvge_at_leftP`, `cvge_dnbhsP` generalized from `realType` to `archiRealFieldType`

### Deprecated

- in `pseudometric_normed_Zmodule.v`:
  + lemma `fun_cvgD` (use `cvgD` instead)
  + lemma `fun_cvgN` (use `cvgN` instead)

### Removed

- in `normed_module.v`,
  + lemmas `cvge_ge` and `cvge_le`, redundant with existing `cvge_to_ge` and `cvge_to_le`
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
