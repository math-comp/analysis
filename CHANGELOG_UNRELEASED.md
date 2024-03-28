# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_recl`

- in `sequences.v`:
  + lemma `nneseries_recl`
- in `lebesgue_integral.v`
  + lemma `ge0_integralZr`
- file `function_spaces.v`
- in `mathcomp_extra.v`
  + lemma `invf_plt`

- in `set_interval.v`
  + lemmas `setDitv1r`, `setDitv1l`
  + lemmas `set_itvxx`, `itv_bndbnd_setU`

- in `reals.v`
  + lemma `abs_ceil_ge`

- in `topology.v`:
  + lemmas `nbhs_infty_ger`, `nbhs0_ltW`, `nbhs0_lt`

- in `normedtype.v`
  + lemma `closed_ball_ball`

- in `numfun.v`
  + lemma `cvg_indic`

- in `lebesgue_integral.v`
  + lemma `locally_integrable_indic`
  + definition `davg`,
    lemmas `davg0`, `davg_ge0`, `davgD`, `continuous_cvg_davg`
  + definition `lim_sup_davg`,
    lemmas `lim_sup_davg_ge0`, `lim_sup_davg_le`,
	`continuous_lim_sup_davg`, `lim_sup_davgB`, `lim_sup_davgT_HL_maximal`
  + definition `lebesgue_pt`,
    lemma `continuous_lebesgue_pt`
  + lemma `integral_setU_EFin`
  + lemmas `integral_set1`, `ge0_integral_closed_ball`, `integral_setD1_EFin`,
    `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`
  + lemma `lebesgue_differentiation`
  + lemma `lebesgue_density`
  + definition `nicely_shrinking`,
    lemmas `nicely_shrinking_gt0`, `nicely_shrinking_lty`, `nice_lebesgue_differentiation`

- in `normedtype.v`:
  + lemma `ball_open_nbhs`

- new file `ftc.v`:
  - lemmas `FTC1`, `continuous_FTC1`

- in file `normedtype.v`,
  + new definition `completely_regular_space`.
  + new lemmas `point_uniform_separator`, and 
    `uniform_completely_regular`.

- in file `classical_sets.v`
  + lemmas `bigcup_series_addn`, `bigcap_series_addn`

- in file `sequences.v`
  + lemma `nneseries_addn`

### Changed
- moved from `topology.v` to `function_spaces.v`: `prod_topology`, 
    `product_topology_def`, `proj_continuous`, `dfwith_continuous`, 
    `proj_open`, `hausdorff_product`, `tychonoff`, `perfect_prod`, 
    `perfect_diagonal`, `zero_dimension_prod`, `totally_disconnected_prod`, 
    `separate_points_from_closed`, `weak_sep_cvg`, `weak_sep_nbhsE`, 
    `weak_sep_openE`, `join_product`, `join_product_continuous`, 
    `join_product_open`, `join_product_inj`, `join_product_weak`, `fct_ent`, 
    `fct_ent_filter`, `fct_ent_refl`, `fct_ent_inv`, `fct_ent_split`, 
    `cvg_fct_entourageP`, `fun_complete`, `fct_ball`, `fct_ball_center`, 
    `fct_ball_sym`, `fct_ball_triangle`, `fct_entourage`, `cvg_switch_1`, 
    `cvg_switch_2`, `cvg_switch`, `uniform_fun`, `uniform_nbhs`, 
    `uniform_entourage`, `restricted_cvgE`, `pointwise_cvgE`, 
    `uniform_fun_family`, `uniform_set1`, `uniform_subset_nbhs`, 
    `uniform_subset_cvg`, `pointwise_uniform_cvg`, `cvg_sigL`, `eq_in_close`, 
    `hausdorrf_close_eq_in`, `uniform_restrict_cvg`, `uniform_nbhsT`, 
    `cvg_uniformU`, `cvg_uniform_set0`, `fam_cvgP`, `family_cvg_subset`, 
    `family_cvg_finite_covers`, `fam_cvgE`, `fam_nbhs`, `fam_compact_nbhs`, 
    `compact_open`, `compact_openK`, `compact_openK_nbhs`, 
    `compact_open_of_nbhs`, `compact_open_def`, `compact_open_cvgP`, 
    `compact_open_open`, `compact_open_fam_compactP`, `compactly_in`, 
    `compact_cvg_within_compact`, `uniform_limit_continuous`, 
    `uniform_limit_continuous_subspace`, `singletons`, 
    `pointwise_cvg_family_singleton`, `pointwise_cvg_compact_family`, 
    `pointwise_cvgP`, `equicontinuous`, `equicontinuous_subset`, 
    `equicontinuous_subset_id`, `equicontinuous_continuous_for`, 
    `equicontinuous_continuous`, `pointwise_precompact`, 
    `pointwise_precompact_subset`, `pointwise_precompact_precompact`, 
    `uniform_pointwise_compact`, `precompact_pointwise_precompact`, 
    `pointwise_cvg_entourage`, `equicontinuous_closure`, `small_ent_sub`, 
    `pointwise_compact_cvg`, `pointwise_compact_closure`, 
    `pointwise_precompact_equicontinuous`, `compact_equicontinuous`, 
    `precompact_equicontinuous`, `Ascoli`, `continuous_curry`, 
    `continuous_uncurry_regular`, `continuous_uncurry`, `curry_continuous`, and 
    `uncurry_continuous`.

- move from `kernel.v` to `measure.v`
  + definition `mset`, `pset`, `pprobability`
  + lemmas `lt0_mset`, `gt1_mset`

- in `measure.v`:
  + definition `subset_sigma_subadditive`
  + factory `isSubsetOuterMeasure`

### Changed

### Renamed

- in `constructive_ereal.v`:
  + `gee_pmull` -> `gee_pMl`
  + `gee_addl` -> `geeDl`
  + `gee_addr` -> `geeDr`
  + `gte_addl` -> `gteDl`
  + `gte_addr` -> `gteDr`
  + `lte_subl_addr` -> `lteBlDr`
  + `lte_subl_addl` -> `lteBlDl`
  + `lte_subr_addr` -> `lteBrDr`
  + `lte_subr_addl` -> `lteBrDl`
  + `lee_subl_addr` -> `leeBlDr`
  + `lee_subl_addl` -> `leeBlDl`
  + `lee_subr_addr` -> `leeBrDr`
  + `lee_subr_addl` -> `leeBrDl`

- in `measure.v`:
  + `sub_additive` -> `subadditive`
  + `sigma_sub_additive` -> `measurable_subset_sigma_subadditive`
  + `content_sub_additive` -> `content_subadditive`
  + `ring_sigma_sub_additive` -> `ring_sigma_subadditive`
  + `Content_SubSigmaAdditive_isMeasure` -> `Content_SigmaSubAdditive_isMeasure`
  + `measure_sigma_sub_additive` -> `measure_sigma_subadditive`
  + `measure_sigma_sub_additive_tail` -> `measure_sigma_subadditive_tail`

### Generalized

- in `constructive_ereal.v`:
  + `gee_pMl` (was `gee_pmull`)

- in `sequences.v`:
  + lemmas `eseries0`, `nneseries_split`

### Deprecated

### Removed

### Infrastructure

### Misc
