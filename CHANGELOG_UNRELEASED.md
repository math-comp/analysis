# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemma `globally0`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`
- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_itv`
- in `lebesgue_integral.v`:
  + lemma `sfinite_Fubini`

- file `itv.v`:
  + definition `wider_itv`
  + module `Itv`:
    * definitions `map_itv_bound`, `map_itv`
    * lemmas `le_map_itv_bound`, `subitv_map_itv`
    * definition `itv_cond`
    * record `def`
    * notation `spec`
    * record `typ`
    * definitions `mk`, `from`, `fromP`
  + notations `{itv R & i}`, `{i01 R}`, `%:itv`, `[itv of _]`, `inum`, `%:inum`
  + definitions `itv_eqMixin`, `itv_choiceMixin`, `itv_porderMixin`
  + canonical `itv_subType`, `itv_eqType`, `itv_choiceType`, `itv_porderType`
  + lemma `itv_top_typ_subproof`
  + canonical `itv_top_typ`
  + lemma `typ_inum_subproof`
  + canonical `typ_inum`
  + notation `unify_itv`
  + lemma `itv_intro`
  + definition `empty_itv`
  + lemmas `itv_bottom`, `itv_gt0`, `itv_le0F`, `itv_lt0`, `itv_ge0F`, `itv_ge0`, `lt0F`, `le0`, `gt0F`, `lt1`,
    `ge1F`, `le1`, `gt1F`
  + lemma `widen_itv_subproof`
  + definition `widen_itv`
  + lemma `widen_itvE`
  + notation `%:i01`
  + lemma `zero_inum_subproof`
  + canonical `zero_inum`
  + lemma `one_inum_subproof`
  + canonical `one_inum`
  + definition `opp_itv_bound_subdef`
  + lemmas `opp_itv_ge0_subproof`, `opp_itv_gt0_subproof`, `opp_itv_boundr_subproof`,
    `opp_itv_le0_subproof`, `opp_itv_lt0_subproof`, `opp_itv_boundl_subproof`
  + definition `opp_itv_subdef`
  + lemma `opp_inum_subproof `
  + canonical `opp_inum`
  + definitions `add_itv_boundl_subdef`, `add_itv_boundr_subdef`, `add_itv_subdef`
  + lemma `add_inum_subproof`
  + canonical `add_inum`
  + definitions `itv_bound_signl`, `itv_bound_signr`, `interval_sign`
  + variant `interval_sign_spec`
  + lemma `interval_signP`
  + definitions `mul_itv_boundl_subdef`, `mul_itv_boundr_subdef`
  + lemmas `mul_itv_boundl_subproof`, `mul_itv_boundrC_subproof`, `mul_itv_boundr_subproof`,
    `mul_itv_boundr'_subproof`
  + definition `mul_itv_subdef`
  + lemmas `map_itv_bound_min`, `map_itv_bound_max`, `mul_inum_subproof`
  + canonical `mul_inum`
  + lemmas `inum_eq`, `inum_le`, `inum_lt`
- in `mathcomp_extra.v`
  + lemma `ler_sqrt`
- in `constructive_ereal.v`
  + definition `sqrte`
  + lemmas `sqrte0`, `sqrte_ge0`, `lee_sqrt`, `sqrteM`, `sqr_sqrte`,
    `sqrte_sqr`, `sqrte_fin_num`
- in `exp.v`:
  + lemma `ln_power_pos`
  + definition `powere_pos`, notation ``` _ `^ _ ``` in `ereal_scope`
  + lemmas `powere_pos_EFin`, `powere_posyr`, `powere_pose0`,
    `powere_pose1`, `powere_posNyr` `powere_pos0r`, `powere_pos1r`,
    `powere_posNyr`, `fine_powere_pos`, `powere_pos_ge0`,
    `powere_pos_gt0`, `powere_pos_eq0`, `powere_posM`, `powere12_sqrt`
- in `measure.v`:
  + lemmas `negligibleU`, `negligibleS`
  + definition `almost_everywhere_notation`
  + instances `ae_filter_ringOfSetsType`, `ae_filter_algebraOfSetsType`,
    `ae_filter_measurableType`
  + instances `ae_properfilter_algebraOfSetsType`, `ae_properfilter_measurableType`

- file `ereal.v`:
  + lemmas `compreBr`, `compre_scale`
  + lemma `le_er_map`
- file `lebesgue_measure.v`
  + lemma `measurable_fun_er_map`
- file `lebesgue_integral.v`:
  + instance of `isMeasurableFun` for `normr`
  + lemma `finite_measure_integrable_cst`
  + lemma `ae_ge0_le_integral`
  + lemma `ae_eq_refl`
- file `probability.v`:
  + definition `random_variable`, notation `{RV _ >-> _}`
  + lemmas `notin_range_measure`, `probability_range`
  + definition `distribution`, instance of `isProbability`
  + lemma `probability_distribution`, `integral_distribution`
  + definition `expectation`, notation `'E_P[X]`
  + lemmas `expectation_cst`, `expectation_indic`, `integrable_expectation`,
    `expectationM`, `expectation_ge0`, `expectation_le`, `expectationD`,
    `expectationB`
  + definition `variance`, `'V_P[X]`
  + lemma `varianceE`
  + lemmas `variance_ge0`, `variance_cst`
  + lemmas `markov`, `chebyshev`,
  + mixin `MeasurableFun_isDiscrete`, structure `discreteMeasurableFun`,
    notation `{dmfun aT >-> T}`
  + definition `discrete_random_variable`, notation `{dRV _ >-> _}`
  + definitions `dRV_dom_enum`, `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV_enum`, `distribution_dRV`, `sum_enum_prob`,
    `dRV_expectation`
  + definion `pmf`, lemma `expectation_pmf`

- in file `topology.v`,
  + new definitions `totally_disconnected`, and `zero_dimensional`.
  + new lemmas `component_closed`, `zero_dimension_prod`, 
    `discrete_zero_dimension`, `zero_dimension_totally_disconnected`, 
    `totally_disconnected_cvg`, and `totally_disconnected_prod`.

- in file `topology.v`,
  + new definitions `split_sym`, `gauge`, `gauge_uniformType_mixin`, 
    `gauge_topologicalTypeMixin`, `gauge_filtered`, `gauge_topologicalType`, 
    `gauge_uniformType`, `gauge_psuedoMetric_mixin`, and 
    `gauge_psuedoMetricType`.
  + new lemmas `iter_split_ent`, `gauge_ent`, `gauge_filter`, 
    `gauge_refl`, `gauge_inv`, `gauge_split`, `gauge_countable_uniformity`, and 
    `uniform_pseudometric_sup`.
  + new definitions `discrete_ent`, `discrete_uniformType`, `discrete_ball`, 
    `discrete_pseudoMetricType`, and `pseudoMetric_bool`.
  + new lemmas `finite_compact`, `discrete_ball_center`, `compact_cauchy_cvg`
- in file `topology.v`,
  + new definitions `basis`, and `second_countable`.
  + new lemmas `clopen_countable` and `compact_countable_base`.

### Changed

- in `mathcomp_extra.v`
  + lemmas `eq_bigmax`, `eq_bigmin` changed to respect `P` in the returned type.
- in `measure.v`:
  + generalize `negligible` to `semiRingOfSetsType`
- in `exp.v`:
  + new lemmas `power_pos_ge0`, `power_pos0`, `power_pos_eq0`,
    `power_posM`, `power_posAC`, `power12_sqrt`, `power_pos_inv1`,
    `power_pos_inv`, `power_pos_intmul`
- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_ln`, `measurable_fun_power_pos`
- in `measure.v`:
  + lemma `measurable_fun_bigcup`
- in `sequences.v`:
  + lemma `eq_eseriesl`

### Changed

### Renamed

- in `derive.v`:
  + `Rmult_rev` -> `mulr_rev`
  + `rev_Rmult` -> `rev_mulr`
  + `Rmult_is_linear` -> `mulr_is_linear`
  + `Rmult_linear` -> `mulr_linear`
  + `Rmult_rev_is_linear` -> `mulr_rev_is_linear`
  + `Rmult_rev_linear` -> `mulr_rev_linear`
  + `Rmult_bilinear` -> `mulr_bilinear`
  + `is_diff_Rmult` -> `is_diff_mulr`

### Generalized

### Deprecated

### Removed

- in `normedtype.v`:
  + instance `Proper_dnbhs_realType`
- in `measure.v`:
  + instances `ae_filter_algebraOfSetsType`, `ae_filter_measurableType`,
  `ae_properfilter_measurableType`

### Infrastructure

### Misc
