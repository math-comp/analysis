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
- in `measure.v`:
  + lemmas `ae_imply`, `ae_imply2`
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
  + mixin `isLfun`, structure `Lfun`, notation `LfunType`
  + canonicals `Lfun_eqType`, `Lfun_choiceType`, `Lequiv_canonical`
  + definition `LType`
  + definitions `Lequiv`, `LspaceType`
  + definition `Lspace`, notation `.-Lspace`
  + lemmas `LequivP`, `LType1_integrable`, `LType2_integrable_sqr`
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
- in `classical_sets.v`:
  + canonical `unit_pointedType`
- in `measure.v`:
  + definition `finite_measure`
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`
  + structures `sigma_finite_additive_measure` and `sigma_finite_measure`

- in file `topology.v`,
  + new definition `perfect_set`.
  + new lemmas `perfectTP`, `perfect_prod`, and `perfect_diagonal`.

- in `constructive_ereal.v`:
  + lemma `oppe_inj`

- in `mathcomp_extra.v`:
  + lemma `add_onemK`
  + function `swap`
- in `classical_sets.v`:
  + lemmas `setT0`, `set_unit`, `set_bool`
  + lemmas `xsection_preimage_snd`, `ysection_preimage_fst`
- in `exp.v`:
  + lemma `expR_ge0`
- in `measure.v`
  + lemmas `measurable_curry`, `measurable_fun_fst`, `measurable_fun_snd`,
    `measurable_fun_swap`, `measurable_fun_pair`, `measurable_fun_if_pair`
  + lemmas `dirac0`, `diracT`
  + lemma `finite_measure_sigma_finite`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_opp`
- in `lebesgue_integral.v`
  + lemmas `integral0_eq`, `fubini_tonelli`
  + product measures now take `{measure _ -> _}` arguments and their
    theory quantifies over a `{sigma_finite_measure _ -> _}`.

- in `classical_sets.v`:
  + lemma `trivIset_mkcond`
- in `numfun.v`:
  + lemmas `xsection_indic`, `ysection_indic`
- in `classical_sets.v`:
  + lemmas `xsectionI`, `ysectionI`
- in `lebesgue_integral.v`:
  + notations `\x`, `\x^` for `product_measure1` and `product_measure2`

- file `ereal.v`:
  + lemmas `compreBr`, `compre_scale`
  + lemma `le_er_map`
- file `lebesgue_integral.v`:
  + instance of `isMeasurableFun` for `normr`
  + lemma `finite_measure_integrable_cst`
  + lemma `measurable_fun_er_map`
- file `probability.v`:
  + definition `Lspace`, notation `.-Lspace`
  + lemmas `Lspace1`, `Lspace2`
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
  + lemmas `markov`, `chebyshev`,
  + mixin `MeasurableFun_isDiscrete`, structure `discreteMeasurableFun`,
    notation `{dmfun aT >-> T}`
  + definition `discrete_random_variable`, notation `{dRV _ >-> _}`
  + definitions `dRV_dom_enum`, `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV_enum`, `distribution_dRV`, `sum_enum_prob`,
    `dRV_expectation`
  + definion `pmf`, lemma `expectation_pmf`

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

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemmas `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd`
    (use `emeasurable_itv` instead)
- in `measure.v`:
  + lemma `measurable_fun_ext`

### Removed

- in `lebesgue_measure.v`:
  + lemma `ae_eq_mul`
  + `emeasurable_fun_bool` -> `measurable_fun_bool`


### Infrastructure

### Misc
