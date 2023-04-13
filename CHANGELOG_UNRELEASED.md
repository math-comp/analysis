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

### Removed

- in `lebesgue_measure.v`:
  + lemma `ae_eq_mul`

### Infrastructure

### Misc
