# Changelog (unreleased)

## [Unreleased]

### Added

- in `sequences.v`:
  + lemmas `seriesN`, `seriesD`, `seriesZ`, `is_cvg_seriesN`, `lim_seriesN`,
    `is_cvg_seriesZ`, `lim_seriesZ`, `is_cvg_seriesD`, `lim_seriesD`,
    `is_cvg_seriesB`, `lim_seriesB`, `lim_series_le`, `lim_series_norm`
- in `classical_sets.v`:
  + lemmas `bigcup_image`, `bigcup_of_set1`
- in `boolp.v`:
  + definitions `equality_mixin_of_Type`, `choice_of_Type`
- in `measure.v`:
  + HB.mixin `AlgebraOfSets_from_RingOfSets`
  + HB.structure `AlgebraOfSets` and notation `algebraOfSetsType`
  + HB.instance `T_isAlgebraOfSets` in HB.builders `isAlgebraOfSets`
  + lemma `bigcup_set_cond`
- in `classical_sets.v`:
  + lemmas `bigcupD1`, `bigcapD1`
- in `measure.v`:
  + definition `measurable_fun`
  + lemma `adde_undef_nneg_series`
- in `measure.v`:
  + lemmas `epsilon_trick`, 
  + definition `measurable_cover`
  + lemmas `cover_measurable`, `cover_subset`
  + definition `mu_ext`
  + lemmas `le_mu_ext`, `mu_ext_ge0`, `mu_ext0`, `measurable_uncurry`,
    `mu_ext_sigma_subadditive`
  + canonical `outer_measure_of_measure`

### Changed

- in `measure.v`:
  + generalize lemma `eq_bigcupB_of`
- in `ereal.v`, definition `adde_undef` changed to `adde_def`
  + consequently, the following lemmas changed:
    * in `ereal.v`, `adde_undefC` renamed to `adde_defC`,
      `fin_num_adde_undef` renamed to `fin_num_adde_def`
    * in `sequences.v`, `ereal_cvgD` and `ereal_limD` now use hypotheses with `adde_def`
- in `sequences.v`:
  + generalize `{in,de}creasing_seqP`, `non{in,de}creasing_seqP` from `numDomainType`
    to `porderType`
- in `measure.v`:
  + HB.mixin `Measurable_from_ringOfSets` changed to `Measurable_from_algebraOfSets`
  + HB.instance `T_isRingOfSets` becomes `T_isAlgebraOfSets` in HB.builders `isMeasurable`
  + lemma `measurableC` now applies to `algebraOfSetsType` instead of `measureableType`
- in `normedtype.v`:
  + lemma `cvg_bounded_real`
  + lemma `pseudoMetricNormedZModType_hausdorff`

### Changed

- in `normedtype.v`:
  + generalized from `normedModType` to `pseudoMetricNormedZmodType`:
    * `nbhs_le_nbhs_norm`
    * `nbhs_norm_le_nbhs`
    * `nbhs_nbhs_norm`
    * `nbhs_normP`
    * `filter_from_norm_nbhs`
    * `nbhs_normE`
    * `filter_from_normE`
    * `near_nbhs_norm`
    * `nbhs_norm_ball_norm`
    * `nbhs_ball_norm`
    * `ball_norm_dec`
    * `ball_norm_sym`
    * `ball_norm_le`
    * `cvg_distP`
    * `cvg_dist`
    * `nbhs_norm_ball`
    * `dominated_by`
    * `strictly_dominated_by`
    * `sub_dominatedl`
    * `sub_dominatedr`
    * `dominated_by1`
    * `strictly_dominated_by1`
    * `ex_dom_bound`
    * `ex_strict_dom_bound`
    * `bounded_near`
    * `boundedE`
    * `sub_boundedr`
    * `sub_boundedl`
    * `ex_bound`
    * `ex_strict_bound`
    * `ex_strict_bound_gt0`
    * `norm_hausdorff`
    * `norm_closeE`
    * `norm_close_eq`
    * `norm_cvg_unique`
    * `norm_cvg_eq`
    * `norm_lim_id`
    * `norm_cvg_lim`
    * `norm_lim_near_cst`
    * `norm_lim_cst`
    * `norm_cvgi_unique`
    * `norm_cvgi_map_lim`
    * `distm_lt_split`
    * `distm_lt_splitr`
    * `distm_lt_splitl`
    * `normm_leW`
    * `normm_lt_split`
    * `cvg_distW`
    * `continuous_cvg_dist`
    * `add_continuous`
- moved from `normedtype.v` to `reals.v`:
  + lemmas `inf_lb_strict`, `sup_ub_strict`
- moved from `sequences.v` to `reals.v`:
  + lemma `has_ub_image_norm`

### Renamed

- in `measure.v`:
  + `isRingOfSets` -> `isAlgebraOfSets`
- in `classical_sets.v`:
  + `bigcup_mkset` -> `bigcup_set`
  + `bigsetU` -> `bigcup`
  + `bigsetI` -> `bigcap`
  + `trivIset_bigUI` -> `trivIset_bigsetUI`
- in `measure.v`:
  + `B_of` -> `seqD`
  + `trivIset_B_of` -> `trivIset_seqD`
  + `UB_of` -> `setU_seqD`
  + `bigUB_of` -> `bigsetU_seqD`
  + `eq_bigsetUB_of` -> `eq_bigsetU_seqD`
  + `eq_bigcupB_of` -> `eq_bigcup_seqD`
  + `eq_bigcupB_of_bigsetU` -> `eq_bigcup_seqD_bigsetU`

### Removed

- in `nngnum.v`:
  + lemma `filter_andb`

### Infrastructure

### Misc
