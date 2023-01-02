# Changelog (unreleased)

## [Unreleased]

### Added

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
  + lemmas `EFin_sum_fine`, `sumeN`
  + lemmas `adde_defDr`, `adde_def_sum`, `fin_num_sumeN`
  + lemma `fin_num_adde_defr`, `adde_defN`

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

- in `constructive_ereal.v`:
  + lemmas `expeS`, `fin_numX`

- in `functions.v`:
  + lemma `countable_bijP`
  + lemma `patchE`
  + lemmas `set_compose_subset`, `compose_diag`
  + notation `\;` for the composition of relations
- OPAM package `coq-mathcomp-classical` containing `boolp.v`
- file `all_classical.v`
- in file `mathcomp_extra.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (from `classical_sets.v`)
  + lemma `sumr_le0`
- in file `fsbigop.v`:
  + lemmas `fsumr_ge0`, `fsumr_le0`, `fsumr_gt0`, `fsumr_lt0`, `pfsumr_eq0`,
    `pair_fsbig`, `exchange_fsbig`
- in file `ereal.v`:
  + notation `\sum_(_ \in _) _` (from `fsbigop.v`)
  + lemmas `fsume_ge0`, `fsume_le0`, `fsume_gt0`, `fsume_lt0`,
    `pfsume_eq0`, `lee_fsum_nneg_subset`, `lee_fsum`,
    `ge0_mule_fsumr`, `ge0_mule_fsuml` (from `fsbigop.v`)
  + lemmas `finite_supportNe`, `dual_fsumeE`, `dfsume_ge0`, `dfsume_le0`,
    `dfsume_gt0`, `dfsume_lt0`, `pdfsume_eq0`, `le0_mule_dfsumr`, `le0_mule_dfsuml`
- file `classical/set_interval.v`
- in file `classical/set_interval.v`:
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`,
    `disjoint_itv`, `conv`, `factor`, `ndconv` (from `set_interval.v`)
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itv_cc`,
    `set_itvco`, `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`,
    `set_itv_infty_infty`, `set_itv_o_infty`, `set_itv_c_infty`, `set_itv_infty_o`,
    `set_itv_infty_c`, `set_itv_pinfty_bnd`, `set_itv_bnd_ninfty`, `setUitv1`,
    `setU1itv`, `set_itvI`, `neitvE`, `neitvP`, `setitv0`, `has_lbound_itv`,
    `has_ubound_itv`, `hasNlbound`, `hasNubound`, `opp_itv_bnd_infty`,
    `opp_itv_infty_bnd`, `opp_itv_bnd_bnd`, `opp_itvoo`,
    `setCitvl`, `setCitvr`, `set_itv_splitI`, `setCitv`, `set_itv_splitD`,
    `mem_1B_itvcc`, `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`,
    `conv1`, `conv_sym`, `conv_flat`, `leW_conv`, `leW_factor`,
    `factor_flat`, `factorl`, `ndconvE`, `factorr`, `factorK`,
    `convK`, `conv_inj`, `factor_inj`, `conv_bij`, `factor_bij`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`, `conv_itv_bij`,
    `factor_itv_bij`, `mem_conv_itv`, `mem_conv_itvcc`, `range_conv`,
    `range_factor`, `mem_factor_itv`,
    `set_itv_ge`, `trivIset_set_itv_nth`, `disjoint_itvxx`, `lt_disjoint`,
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (from `set_interval.v`)
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (from `reals.v`)
- in `classical_sets.v`:
  + lemma `bigsetU_sup`
- in `lebesgue_integral.v`:
  + lemmas `emeasurable_fun_fsum`, `ge0_integral_fsum`
- in `ereal.v`:
  + lemma `fsumEFin`
- in `lebesgue_measure.v`:
  + definition `ErealGenInftyO.R` and lemma `ErealGenInftyO.measurableE`
  + lemma `sub1set`
- in `constructive_ereal.v`:
  + lemmas `lteN10`, `leeN10`
  + lemmas `le0_fin_numE`
  + lemmas `fine_lt0`, `fine_le0`
- in `sequences.v`:
  + lemmas `is_cvg_ereal_npos_natsum_cond`, `lee_npeseries`,
    `is_cvg_npeseries_cond`, `is_cvg_npeseries`, `npeseries_le0`,
    `is_cvg_ereal_npos_natsum`
  + lemma `nnseries_is_cvg`
- in `constructive_ereal.v`:
  + lemma `fine_lt0E`
- in file `normedtype.v`
  + lemmas `closed_ballR_compact` and `locally_compactR`

- in `sequences.v`:
  + lemma `invr_cvg0` and `invr_cvg_pinfty`
  + lemma `cvgPninfty_lt`, `cvgPpinfty_near`, `cvgPninfty_near`,
    `cvgPpinfty_lt_near` and `cvgPninfty_lt_near`
- in `classical_sets.v`:
  + notations `\bigcup_(i < n) F` and `\bigcap_(i < n) F`
- in `topoogy.v`
  + definitions `sup_pseudoMetricType`, `product_pseudoMetricType`

- in `fsbig.v`:
  + lemma `fsbig_setU_set1`
- in `tooplogy.v`:
  + lemmas `closed_bigsetU`, `accessible_finite_set_closed`


- in file `classical_sets.v`,
  + new lemmas `eq_image_id`, `subKimage`, `subimageK`, and `eq_imageK`.
- in file `functions.v`,
  + new lemmas `inv_oppr`, `preimageEoinv`, `preimageEinv`, and
    `inv_funK`.
- in file `mathcomp_extra.v`,
  + new definition `inv_fun`.
  + new lemmas `ler_ltP`, and `real_ltr_distlC`.
- in file `constructive_ereal.v`,
  + new lemmas `real_ltey`, `real_ltNye`, `real_leey`, `real_leNye`,
    `fin_real`, `addNye`, `addeNy`, `gt0_muley`, `lt0_muley`, `gt0_muleNy`, and
    `lt0_muleNy`.
  + new lemmas `daddNye`, and `daddeNy`.
- in file `ereal.v`,
  + new lemmas `ereal_nbhs_pinfty_gt`, `ereal_nbhs_ninfty_lt`,
    `ereal_nbhs_pinfty_real`, and `ereal_nbhs_ninfty_real`.
- in file `normedtype.v`,
  + new lemmas `nbhsNimage`, `nbhs_pinfty_real`, `nbhs_ninfty_real`,
    `pinfty_ex_ge`, `cvgryPger`, `cvgryPgtr`, `cvgrNyPler`, `cvgrNyPltr`,
    `cvgry_ger`, `cvgry_gtr`, `cvgrNy_ler`, `cvgrNy_ltr`, `cvgNry`, `cvgNrNy`,
    `cvgry_ge`, `cvgry_gt`, `cvgrNy_le`, `cvgrNy_lt`, `cvgeyPger`, `cvgeyPgtr`,
    `cvgeyPgty`, `cvgeyPgey`, `cvgeNyPler`, `cvgeNyPltr`, `cvgeNyPltNy`,
    `cvgeNyPleNy`, `cvgey_ger`, `cvgey_gtr`, `cvgeNy_ler`, `cvgeNy_ltr`,
    `cvgNey`, `cvgNeNy`, `cvgerNyP`, `cvgeyPge`, `cvgeyPgt`, `cvgeNyPle`,
    `cvgeNyPlt`, `cvgey_ge`, `cvgey_gt`, `cvgeNy_le`, `cvgeNy_lt`, `cvgenyP`,
    `normfZV`, `fcvgrPdist_lt`, `cvgrPdist_lt`, `cvgrPdistC_lt`,
    `cvgr_dist_lt`, `cvgr_distC_lt`, `cvgr_dist_le`, `cvgr_distC_le`,
    `nbhs_norm0P`, `cvgr0Pnorm_lt`, `cvgr0_norm_lt`, `cvgr0_norm_le`, `nbhsDl`,
    `nbhsDr`, `nbhs0P`, `nbhs_right0P`, `nbhs_left0P`, `nbhs_right_gt`,
    `nbhs_left_lt`, `nbhs_right_neq`, `nbhs_left_neq`, `nbhs_right_ge`,
    `nbhs_left_le`, `nbhs_right_lt`, `nbhs_right_le`, `nbhs_left_gt`,
    `nbhs_left_ge`, `nbhsr0P`, `cvgrPdist_le`, `cvgrPdist_ltp`,
    `cvgrPdist_lep`, `cvgrPdistC_le`, `cvgrPdistC_ltp`, `cvgrPdistC_lep`,
    `cvgr0Pnorm_le`, `cvgr0Pnorm_ltp`, `cvgr0Pnorm_lep`, `cvgr_norm_lt`,
    `cvgr_norm_le`, `cvgr_norm_gt`, `cvgr_norm_ge`, `cvgr_neq0`,
    `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_gt`, `real_cvgr_ge`, `cvgr_lt`,
    `cvgr_gt`, `cvgr_norm_lty`, `cvgr_norm_ley`, `cvgr_norm_gtNy`,
    `cvgr_norm_geNy`, `fcvgr_dist_lt2P`, `cvgr_dist_lt2P`, `cvgr_dist_lt2`,
    `cvgNP`, `norm_cvg0P`, `cvgVP`, `is_cvgVE`, `cvgr_to_ge`, `cvgr_to_le`,
    `nbhs_EFin`, `nbhs_ereal_pinfty`, `nbhs_ereal_ninfty`, `fine_fcvg`,
    `fcvg_is_fine`, `fine_cvg`, `cvg_is_fine`, `cvg_EFin`, `neq0_fine_cvgP`,
    `cvgeNP`, `is_cvgeNE`, `cvge_to_ge`, `cvge_to_le`, `is_cvgeM`, `limeM`,
    `cvge_ge`, `cvge_le`, `lim_nnesum`, `ltr0_cvgV0`, `cvgrVNy`, `ler_cvg_to`,
    `gee_cvgy`, `lee_cvgNy`, `squeeze_fin`, and `lee_cvg_to`.
- in file `sequences.v`,
  + new lemma `nneseries_pinfty`.
- in file `topology.v`,
  + new definitions `countable_uniformity`, `countable_uniformityT`, 
    `sup_pseudoMetric_mixin`, `sup_pseudoMetricType`, and 
    `product_pseudoMetricType`.
  + new lemmas `countable_uniformityP`, `countable_sup_ent`, and 
    `countable_uniformity_metric`.

- in `constructive_ereal.v`:
  + lemmas `adde_def_doppeD`, `adde_def_doppeB`
  + lemma `fin_num_sume_distrr`
- in `classical_sets.v`:
  + lemma `coverE`

- in file `topology.v`,
  + new definitions `quotient_topology`, and `quotient_open`.
  + new lemmas `pi_continuous`, `quotient_continuous`, and
    `repr_comp_continuous`.

- in file `boolp.v`,
  + new lemma `forallp_asboolPn2`.
- in file `classical_sets.v`,
  + new lemma `preimage_range`.
- in file `topology.v`,
  + new definitions `hausdorff_accessible`, `separate_points_from_closed`, and 
    `join_product`.
  + new lemmas `weak_sep_cvg`, `weak_sep_nbhsE`, `weak_sep_openE`, 
    `join_product_continuous`, `join_product_open`, `join_product_inj`, and 
    `join_product_weak`. 

### Changed

- in `fsbigop.v`:
  + implicits of `eq_fsbigr`
- move from `lebesgue_integral.v` to `classical_sets.v`
  + lemmas `trivIset_preimage1`, `trivIset_preimage1_in`
- move from `lebesgue_integral.v` to `numfun.v`
  + lemmas `fimfunE`, `fimfunEord`, factory `FiniteDecomp`
  + lemmas `fimfun_mulr_closed`
  + canonicals `fimfun_mul`, `fimfun_ring`, `fimfun_ringType`
  + defintion `fimfun_ringMixin`
  + lemmas `fimfunM`, `fimfun1`, `fimfun_prod`, `fimfunX`,
    `indic_fimfun_subproof`.
  + definitions `indic_fimfun`, `scale_fimfun`, `fimfun_comRingMixin`
  + canonical `fimfun_comRingType`
  + lemma `max_fimfun_subproof`
  + mixin `IsNonNegFun`, structure `NonNegFun`, notation `{nnfun _ >-> _}`

### Renamed

- in `measurable.v`:
  + `measurable_fun_comp` -> `measurable_funT_comp`
- in `numfun.v`:
  + `IsNonNegFun` -> `isNonNegFun`
- in `lebesgue_integral.v`:
  + `IsMeasurableFunP` -> `isMeasurableFun`
- in `measure.v`:
  + `{additive_measure _ -> _}` -> `{content _ -> _}`
  + `isAdditiveMeasure` -> `isContent`
  + `AdditiveMeasure` -> `Content`
  + `additive_measure` -> `content`
  + `additive_measure_snum_subproof` -> `content_snum_subproof`
  + `additive_measure_snum` -> `content_snum`
  + `SigmaFiniteAdditiveMeasure` -> `SigmaFiniteContent`
  + `sigma_finite_additive_measure` -> `sigma_finite_content`
  + `{sigma_finite_additive_measure _ -> _}` -> `{sigma_finite_content _ -> _}`
- in `constructive_ereal.v`:
  + `fin_num_adde_def` -> `fin_num_adde_defl`
  + `oppeD` -> `fin_num_oppeD`
  + `oppeB` -> `fin_num_oppeB`
  + `doppeD` -> `fin_num_doppeD`
  + `doppeB` -> `fin_num_doppeB`
- in `topology.v`:
  + `finSubCover` -> `finite_subset_cover`

### Generalized

- in `esum.v`:
  + lemma `esum_esum`
- in `measure.v`
  + lemma `measurable_fun_comp`
- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`
- in `measure.v`:
  + lemma `measure_bigcup` generalized,
- in `classical_sets.v`:
  + `xsection_preimage_snd`, `ysection_preimage_fst`
- in `constructive_ereal.v`:
  + `oppeD`, `oppeB`

### Deprecated

### Removed

- in `esum.v`:
  + lemma `fsbig_esum`

### Infrastructure

### Misc
