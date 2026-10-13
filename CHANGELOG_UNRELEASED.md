# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`
- in file `real_interval.v`,
  + new lemmas `itv_cNyNye`, `itv_oNyNye`, `itv_cNyye`, `itv_oNyye`, `itv_ccNyeye`, 
    `itv_coNyeye`, `itv_ocNyeye`, `itv_ooNyeye`, `itv_oNyey_bigcup`, 
    `itv_oNyye_bigcup`.
- in `lebesgue_integral_nonneg.v`,
  + new lemma `integral_itvD`.
- in `lebesgue_integral_under.v`,
  + new lemma `econtinuity_under_integral`.
- in `ereal_normedtype.v`,
  + new lemmas `nbhs_right_lte`, `nbhs_left_gte`, `nbhs_right_lee`, `nbhs_left_gee`.
- in `normed_module.v`,
  + new lemmas `within_econtinuousD`, `within_econtinuousN`, 
    `within_econtinuousB`, `within_econtinuousM`, `within_continuous_fine`, 
    `within_econtinuous_EFin`, `cvge_lt`, `cvge_gt`, `cvge_ge`, `cvge_le`.
- in `num_normedtype.v`,
  + new lemmas `continuous_within_itvbbP`,
    `continuous_within_itvocP`, `continuous_within_itvcoP`, 
    `continuous_within_itvbyP`, `continuous_within_itvNybP`.
- in `num_topology.v`,
  + new lemma `not_nearP`.
- in `pseudometric_structure.v`,
  + new lemma `cvg_withinP`.

### Changed

- moved from `pseudometric_normed_Zmodule.v` to `num_normedtype.v`:
  + lemmas `continuous_within_itvP`, `continuous_within_itvcyP`, `continuous_within_itvNycP`, `within_continuous_continuous`.
- moved from `pseudometric_normed_Zmodule.v` to `num_topology.v`:
  + lemmas `cvg_at_right_filter`, 
    `cvg_at_left_filter`, `cvg_at_right_within`, `cvg_at_left_within`.

### Renamed

- in `real_interval.v`:
  + `itv_cyy` -> `itv_cyey`
  + `itv_oyy` -> `itv_oyey`
  + `itv_cNyy` -> `itv_cNyey`
  + `itv_oNyy` -> `itv_oNyey`
- in `pseudometric_normed_Zmodule.v`:
  + `continuous_within_itvP` -> `continuous_within_itvccP`

### Generalized

- in `num_normedtype.v`: 
    `continuous_within_itvcyP`, 
    `continuous_within_itvNycP`, `continuous_within_itvP`, 
    `within_continuous_continuous` generalized from `pseudoMetricNormedZmodType` to `pseudoMetricType`.
- in `pseudometric_structure.v`: 
  + lemma `cvg_nbhsP` generalized from `metricType` to `pseudoMetricType`.
- in `realfun.v`:
  + lemmas `cvg_at_rightP`, `cvg_at_leftP`, `cvgr_dnbhsP`, `cvge_at_rightP`, `cvge_at_leftP`, `cvge_dnbhsP` generalized from `realType` to `archiRealFieldType` 
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

- in `unstable.v`:
  + definitions `clamp`, `clamp_gele`
  + lemmas `clamp_gemin`, `clamp_lemax`, `minmax_clamp`,
    `clamp_id`, `clamp_min`, `clamp_max`

- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

- new file `edist.v`

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
