# Changelog (unreleased)

## [Unreleased]

### Added

- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_itv`
- in `lebesgue_integral.v`:
  + lemma `sfinite_Fubini`
- in `classical_sets.v`:
  + lemmas `ltn_trivIset`, `subsetC_trivIset`
- in `sequences.v`:
  + lemma `seqDUIE`
- file `charge.v`:
  + mixin `isAdditiveCharge`, structure `AdditiveCharge`, notations
    `additive_charge`, `{additive_charge set T -> \bar R}`
  + mixin `isCharge`, structure `Charge`, notations `charge`,
    `{charge set T -> \bar R}`
  + lemmas `charge0`, `charge_semi_additiveW`, `charge_semi_additive2E`,
    `charge_semi_additive2`, `chargeU`, `chargeDI`, `chargeD`,
    `charge_partition`
  + definitions `crestr`, `cszero`, `cscale`, `positive_set`, `negative_set`
  + lemmas `negative_set_charge_le0`, `negative_set0`, `bigcup_negative_set`,
    `negative_setU`, `positive_negative0`
  + definition `hahn_decomposition`
  + lemmas `hahn_decomposition_lemma`, `Hahn_decomposition`, `Hahn_decomposition_uniq`

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

- in `set_interval.v`:
  + lemma `onem_factor`
- in `set_interval.v`:
  + lemmas `in1_subset_itv`, `subset_itvW`
- in `normedtype.v`:
  + lemmas `cvg_at_right_filter`, `cvg_at_left_filter`,
    `cvg_at_right_within`, `cvg_at_left_within`
- in `derive.v`:
  + lemma `derivable_within_continuous`
- in `realfun.v`:
  + definition `derivable_oo_continuous_bnd`, lemma `derivable_oo_continuous_bnd_within`
- in `exp.v`:
  + lemmas `derive_expR`, `convex_expR`
- new file `convex.v`:
  + mixin `isConvexSpace`, structure `ConvexSpace`, notations `convType`,
    `_ <| _ |> _`
  + lemmas `conv1`, `second_derivative_convex`

- in `mathcomp_extra.v`:
  + lemma `lt_min_lt`
- in `constructive_ereal.v`:
  + lemmas `EFin_min`, `EFin_max`

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
  + definition `almost_everywhere`

### Changed

- in `exp.v`:
  + generalize `exp_fun` and rename to `power_pos`
  + `exp_fun_gt0` has now a condition and is renamed to `power_pos_gt0`
  + remove condition of `exp_funr0` and rename to `power_posr0`
  + weaken condition of `exp_funr1` and rename to `power_posr1`
  + weaken condition of `exp_fun_inv` and rename to `power_pos_inv`
  + `exp_fun1` -> `power_pos1`
  + rename `ler_exp_fun` to `ler_power_pos`
  + `exp_funD` -> `power_posD`
  + weaken condition of `exp_fun_mulrn` and rename to `power_pos_mulrn`
  + the notation ``` `^ ``` has now scope `real_scope`
  + weaken condition of `riemannR_gt0` and `dvg_riemannR`
- in `constructive_ereal.v`:
  + `maxEFin` changed to `fine_max`
  + `minEFin` changed to `fine_min`


### Renamed

- in `lebesgue_measure.v`:
  + `punct_eitv_bnd_pinfty` -> `punct_eitv_bndy`
  + `punct_eitv_ninfty_bnd` -> `punct_eitv_Nybnd`
  + `eset1_pinfty` -> `eset1y`
  + `eset1_ninfty` -> `eset1Ny`
  + `ErealGenOInfty.measurable_set1_ninfty` -> `ErealGenOInfty.measurable_set1Ny`
  + `ErealGenOInfty.measurable_set1_pinfty` -> `ErealGenOInfty.measurable_set1y`
  + `ErealGenCInfty.measurable_set1_ninfty` -> `ErealGenCInfty.measurable_set1Ny`
  + `ErealGenCInfty.measurable_set1_pinfty` -> `ErealGenCInfty.measurable_set1y`
- in `topology.v`:
  + `Topological.ax1` -> `Topological.nbhs_pfilter`
  + `Topological.ax2` -> `Topological.nbhsE`
  + `Topological.ax3` -> `Topological.openE`
  + `entourage_filter` -> `entourage_pfilter`
  + `Uniform.ax1` -> `Uniform.entourage_filter`
  + `Uniform.ax2` -> `Uniform.entourage_refl`
  + `Uniform.ax3` -> `Uniform.entourage_inv`
  + `Uniform.ax4` -> `Uniform.entourage_split_ex`
  + `Uniform.ax5` -> `Uniform.nbhsE`
  + `PseudoMetric.ax1` -> `PseudoMetric.ball_center`
  + `PseudoMetric.ax2` -> `PseudoMetric.ball_sym`
  + `PseudoMetric.ax3` -> `PseudoMetric.ball_triangle`
  + `PseudoMetric.ax4` -> `PseudoMetric.entourageE`
- in `functions.v`:
  + `IsFun` -> `isFun`

- in `set_interval.v`:
  + `conv` -> `line_path`
  + `conv_id` -> `line_path_id`
  + `ndconv` -> `ndline_path`
  + `convEl` -> `line_pathEl`
  + `convEr` -> `line_pathEr`
  + `conv10` -> `line_path10`
  + `conv0` -> `line_path0`
  + `conv1` -> `line_path1`
  + `conv_sym` -> `line_path_sym`
  + `conv_flat` -> `line_path_flat`
  + `leW_conv` -> `leW_line_path`
  + `ndconvE` -> `ndline_pathE`
  + `convK` -> `line_pathK`
  + `conv_inj` -> `line_path_inj`
  + `conv_bij` -> `line_path_bij`
  + `le_conv` -> `le_line_path`
  + `lt_conv` -> `lt_line_path`
  + `conv_itv_bij` -> `line_path_itv_bij`
  + `mem_conv_itv` -> `mem_line_path_itv`
  + `mem_conv_itvcc` -> `mem_line_path_itvcc`
  + `range_conv` -> `range_line_path`

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemmas `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd`
    (use `emeasurable_itv` instead)
- in `measure.v`:
  + lemma `measurable_fun_ext`
- in `realsum.v`:
  + `psumB`, `interchange_sup`, `interchange_psum`
- in `distr.v`:
  + `dlet_lim`, `dlim_let`, `exp_split`, `exp_dlet`,
    `dlet_dlet`, `dmargin_dlet`, `dlet_dmargin`,
    `dfst_dswap`, `dsnd_dswap`, `dsndE`, `pr_dlet`,
    `exp_split`, `exp_dlet`

### Removed

- in `lebesgue_measure.v`:
  + lemma `ae_eq_mul`
  + `emeasurable_fun_bool` -> `measurable_fun_bool`

### Infrastructure

### Misc
