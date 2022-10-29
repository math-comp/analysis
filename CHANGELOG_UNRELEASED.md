# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemmas `continuous_subspaceT`, `subspaceT_continuous`
- in `constructive_ereal.v`
  + lemmas `fine_le`, `fine_lt`, `fine_abse`, `abse_fin_num`
- in `lebesgue_integral.v`
  + lemmas `integral_fune_lt_pinfty`, `integral_fune_fin_num`
- in `topology.v`
  + lemma `weak_subspace_open`
  + lemma `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`, `weak_ent_split`,
      `weak_ent_nbhs`
  + definition `map_pair`, `weak_ent`, `weak_uniform_mixin`, `weak_uniformType`
  + lemma `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
      `sup_ent_nbhs`
  + definition `sup_ent`, `sup_uniform_mixin`, `sup_uniformType`
  + definition `product_uniformType`
  + lemma `uniform_entourage`
  + definition `weak_ball`, `weak_pseudoMetricType`
  + lemma `weak_ballE`
  + lemma `finI_from_countable`
- in `cardinality.v`
  + lemmas `eq_card1`, `card_set1`, `card_eqSP`, `countable_n_subset`,
     `countable_finite_subset`, `eq_card_fset_subset`, `fset_subset_countable`
- in `classical_sets.v`
  + lemmas `IIDn`, `IISl`
- in `mathcomp_extra.v`
  + lemma `lez_abs2n`
- in `constructive_ereal.v`:
  + lemmas `gte_addl`, `gte_addr`
  + lemmas `gte_daddl`, `gte_daddr`
  + lemma `lte_spadder`, `lte_spaddre`
  + lemma `lte_spdadder`
- in `constructive_ereal.v`:
  + lemma `sum_fine`
- in `topology.v`
  + lemmas `entourage_invI`, `split_ent_subset`
  + definition `countable_uniform_pseudoMetricType_mixin`
- in `reals.v`:
  + lemma `floor0`
- in `classical_sets.v`:
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

- in `fsbig.v`:
  + lemma `fsbig_setU_set1`
- in `tooplogy.v`:
  + lemmas `closed_bigsetU`, `accessible_finite_set_closed`
- in file `classical_sets.v`
  + new lemmas `eq_image_id`, `subKimage`, `subimageK`, and `eq_imageK`.
- in file `functions.v`
  + new lemmas `inv_oppr`, `preimageEoinv`, `preimageEinv`, and `inv_funK`.
- in file `mathcomp_extra.v`
  + new Definition `inv_fun`
  + new lemmas `ler_gtP`, and `ler_ltP`.
- in file `constructive_ereal.v`
  + new lemmas `real_ltey`, `real_ltNye`, `real_leey`, `real_leNye`, `fin_real`, `addNye`, `addeNy`, `esumNyP`, `esumyP`, `desumyP`, `desumNyP`, `eqyP`, `gt0_muley`, `lt0_muley`, `gt0_muleNy`, and `lt0_muleNy`.
- in file `derive.v`
  + new lemmas `le0r_fcvg`, `ler0_fcvg`, and `ler_fcvg`.
- in file `ereal.v`
  + new lemmas `ereal_nbhs_pinfty_gt`, `ereal_nbhs_ninfty_lt`, `ereal_nbhs_pinfty_real`, and `ereal_nbhs_ninfty_real`.
- in file `lebesgue_measure.v`
  + new Lemma `measurable_fun_lim_esup`
- in file `normedtype.v`
  + new lemmas `nbhsNimage`, `nbhs_pinfty_real`, `nbhs_ninfty_real`, `pinfty_ex_ge`, `cvgryPger`, `cvgryPgtr`, `cvgryPgty`, `cvgryPgey`, `cvgrNyPler`, `cvgrNyPltr`, `cvgrNyPltNy`, `cvgrNyPleNy`, `cvgry_ger`, `cvgry_gtr`, `cvgrNy_ler`, `cvgrNy_ltr`, `cvgrNy`, `cvgNrNy`, `cvgryPge`, `cvgryPgt`, `cvgrNyPle`, `cvgrNyPlt`, `cvgry_ge`, `cvgry_gt`, `cvgrNy_le`, `cvgrNy_lt`, `cvgrnyP`, `cvgeyPger`, `cvgeyPgtr`, `cvgeyPgty`, `cvgeyPgey`, `cvgeNyPler`, `cvgeNyPltr`, `cvgeNyPltNy`, `cvgeNyPleNy`, `cvgey_ger`, `cvgey_gtr`, `cvgeNy_ler`, `cvgeNy_ltr`, `cvgNey`, `cvgNeNy`, `cvgeryP`, `cvgerNyP`, `cvgeyPge`, `cvgeyPgt`, `cvgeNyPle`, `cvgeNyPlt`, `cvgey_ge`, `cvgey_gt`, `cvgeNy_le`, `cvgeNy_lt`, `cvgenyP`, `normrZ`, `normfZV`, `fcvgrPdist_lt`, `cvgrPdist_lt`, `cvgrPdistC_lt`, `cvgr_dist_lt`, `cvgr_distC_lt`, `cvgr_dist_le`, `cvgr_distC_le`, `nbhs_norm0P`, `cvgr0Pnorm_lt`, `cvgr0_norm_lt`, `cvgr0_norm_le`, `nbhsDl`, `nbhsDr`, `nbhs0P`, `real_ltr_distlC`, `filter_imply`, `nbhs_right0P`, `nbhs_left0P`, `nbhs_right_gt`, `nbhs_left_lt`, `nbhs_right_neq`, `nbhs_left_neq`, `nbhs_right_ge`, `nbhs_left_le`, `nbhs_right_lt`, `nbhs_right_le`, `nbhs_left_gt`, `nbhs_left_ge`, `nbhsr0P`, `cvgrPdist_le`, `cvgrPdist_ltp`, `cvgrPdist_lep`, `cvgrPdistC_le`, `cvgrPdistC_ltp`, `cvgrPdistC_lep`, `cvgr0Pnorm_le`, `cvgr0Pnorm_ltp`, `cvgr0Pnorm_lep`, `cvgr_norm_lt`, `cvgr_norm_le`, `cvgr_norm_gt`, `cvgr_norm_ge`, `cvgr_neq0`, `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_gt`, `real_cvgr_ge`, `cvgr_lt`, `cvgr_le`, `cvgr_gt`, `cvgr_ge`, `cvgr_norm_lty`, `cvgr_norm_ley`, `cvgr_norm_gtNy`, `cvgr_norm_geNy`, `fcvgr_dist_lt2P`, `cvgr_dist_lt2P`, `cvgr_dist_lt2`, `cvgNP`, `norm_cvg0P`, `cvgVP`, `is_cvgVE`, `cvg_ge`, `cvg_le`, `nbhs_EFin`, `nbhs_ereal_pinfty`, `nbhs_ereal_ninfty`, `fine_fcvg`, `fcvg_is_fine`, `fine_cvg`, `cvg_is_fine`, `cvg_EFin`, `fine_cvgP`, `neq0_fine_cvgP`, `cvgeD`, `cvgeN`, `cvgeB`, `cvge_sub0`, `is_cvgeN`, `cvgeMl`, `is_cvgeMl`, `cvgeMr`, `is_cvgeMr`, `cvg_abse0P`, `cvgeM`, `lim_gee`, `lim_lee`, `is_cvgeD`, `limeD`, `limeMl`, `limeMr`, `is_cvgeM`, `limeM`, `limeN`, `cvge_ge`, `cvge_le`, `lim_nnesum`, `gt0_cvgV0`, `cvgVy`, `lt0_cvgV0`, `cvgVNy`, `ger_cvgy`, `ler_cvgNy`, `gee_cvgy`, `lee_cvgNy`, `fin_squeeze`, `esqueeze`, `continuous_linear_bounded`, and `bounded_linear_continuous`.
- in file `sequences.v`
  + new definitions `lim_esup`, and `lim_einf`.
  + new lemmas `nneseries_pinfty`, `lim_einf_shift`, `lim_esup_le_cvg`, `lim_einfN`, `lim_esupN`, `lim_einf_sup`, `cvgNy_lim_einf_sup`, `cvgNy_einfs`, `cvgNy_esups`, `cvgy_einfs`, `cvgy_esups`, `cvg_lim_einf_sup`, `is_cvg_lim_einfE`, and `is_cvg_lim_esupE`.
- in file `topology.v`
  + new lemmas `eq_near`, `cvgNpoint`, `near_fun`, `cvgnyPge`, `cvgnyPgt`, `cvgnyPgty`, `cvgnyPgey`, `fcvg_ballP`, `fcvg_ballPpos`, `fcvg_ball`, and `fcvg_ball2P`.

### Changed
- in `topology.v`
  + definition `fct_restrictedUniformType` changed to use `weak_uniformType`
  + definition `family_cvg_topologicalType` changed to use `sup_uniformType`

- in `constructive_ereal.v`:
  + lemmas `lee_paddl`, `lte_paddl`, `lee_paddr`, `lte_paddr`,
    `lte_spaddr`, `lee_pdaddl`, `lte_pdaddl`, `lee_pdaddr`,
    `lte_pdaddr`, `lte_spdaddr` generalized to `realDomainType`
- in `constructive_ereal.v`:
  + generalize `lte_addl`, `lte_addr`, `gte_subl`, `gte_subr`,
    `lte_daddl`, `lte_daddr`, `gte_dsubl`, `gte_dsubr`
- in `topology.v`:
  + lemmas `continuous_subspace0`, `continuous_subspace1`

- in `realfun.v`:
  + Instance for `GRing.opp` over real intervals

- in `realfun.v`
  + lemmas `itv_continuous_inj_le`, `itv_continuous_inj_ge`,
     `itv_continuous_inj_mono`, `segment_continuous_inj_le`,
     `segment_continuous_inj_ge`, `segment_can_le` ,
     `segment_can_ge`, `segment_can_mono`,
     `segment_continuous_surjective`, `segment_continuous_le_surjective`,
     `segment_continuous_ge_surjective`, `continuous_inj_image_segment`,
     `continuous_inj_image_segmentP`, `segment_continuous_can_sym`,
     `segment_continuous_le_can_sym`, `segment_continuous_ge_can_sym`,
     `segment_inc_surj_continuous`, `segment_dec_surj_continuous`,
     `segment_mono_surj_continuous`, `segment_can_le_continuous`,
     `segment_can_ge_continuous`, `segment_can_continuous`
     all have "{in I, continuous f}" replaced by "{within I, continuous f}"


- in `lebesgue_measure.v`:
  + definition `fimfunE` now uses fsbig
- in `sequence.v`:
  + `nneseries_pinfty` generalized to `eseries_pinfty`

### Renamed

- in `topology.v`:
  + renamed `continuous_subspaceT` to `continuous_in_subspaceT`
- in `constructive_ereal.v`:
  + `lte_spdaddr` -> `lte_spdaddre`
- in `topology.v`:
 + `pasting` -> `withinU_continuous`
- file `theories/boolp.v` -> `classical/boolp.v`
- file `theories/classical_sets.v` -> `classical/classical_sets.v`
- file `theories/functions.v` -> `classical/functions.v`
- file `theories/cardinality.v` -> `classical/cardinality.v`
- file `theories/fsbigop.v` -> `classical/fsbigop.v`
- in `sequences.v`:
  + `nneseries0` -> `eseries0`
  + `nneseries_pred0` -> `eseries_pred0`
  + `eq_nneseries` -> `eq_eseries`
  + `nneseries_mkcond` -> `eseries_mkcond`
- in `mathcomp_extra.v`:
  + `homo_le_bigmax` -> `le_bigmax2`
- in `sequences.v`:
  + `seqDUE` -> `seqDU_seqD`
- file `theories/mathcomp_extra.v` moved to `classical/mathcomp_extra.v`
- `theories/set_interval.v` -> `theories/real_interval.v`

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr`, renamed `lte_spaddre`

### Removed

- in file `classical_sets.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (moved to `mathcomp_extra.v`)
- in file `fsbigop.v`:
  + notation `\sum_(_ \in _) _` (moved to `ereal.v`)
  + lemma `lee_fsum_nneg_subset`, `lee_fsum`, `ge0_mule_fsumr`,
    `ge0_mule_fsuml`, `fsume_ge0`, `fsume_le0`, `fsume_gt0`,
    `fsume_lt0`, `pfsume_eq0` (moved to `ereal.v`)
  + lemma `pair_fsum` (subsumed by `pair_fsbig`)
  + lemma `exchange_fsum` (subsumed by `exchange_fsbig`)
- in file `reals.v`:
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (moved to `classical/set_interval.v`)
- in file `set_interval.v`:
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`,
    `disjoint_itv`, `conv`, `factor`, `ndconv` (moved to `classical/set_interval.v`)
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
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (moved to `classical/set_interval.v`)

- in file `constructive_ereal.v`
  + removed lemmas `esum_ninftyP`, `esum_pinftyP`, `desum_pinftyP`, `desum_ninftyP`, and `eq_pinftyP`.
- in file `derive.v`
  + removed lemmas `le0r_cvg_map`, `ler0_cvg_map`, and `ler_cvg_map`.
- in file `lebesgue_measure.v`
  + removed Lemma `measurable_fun_elim_sup`
- in file `normedtype.v`
  + removed lemmas `normmZ`, `cvg_distP`, `cvg_dist`, `cvg_gt_ge`, `cvg_lt_le`, `cvg_distW`, `cvg_bounded_real`, `continuous_cvg_dist`, `cvg_dist2P`, `cvg_dist2`, `cvg_dist0`, `ereal_cvgN`, `ereal_is_cvgN`, `ereal_cvgrM`, `ereal_is_cvgrM`, `ereal_cvgMr`, `ereal_is_cvgMr`, `ler0_addgt0P`, `ereal_limrM`, `ereal_limMr`, `ereal_limN`, `linear_continuous0`, and `linear_bounded0`.
- in file `sequences.v`
  + removed definitions `elim_sup`, and `elim_inf`.
  + removed lemmas `cvgPpinfty`, `cvgNpinfty`, `cvgNninfty`, `cvgPninfty`, `ger_cvg_pinfty`, `ler_cvg_ninfty`, `cvgPpinfty_lt`, `cvgPninfty_lt`, `cvgPpinfty_near`, `cvgPninfty_near`, `cvgPpinfty_lt_near`, `cvgPninfty_lt_near`, `invr_cvg0`, `invr_cvg_pinfty`, `nat_dvg_real`, `nat_cvgPpinfty`, `ereal_cvg_abs0`, `ereal_cvg_ge0`, `ereal_lim_ge`, `ereal_lim_le`, `dvg_ereal_cvg`, `ereal_cvg_real`, `ereal_cvgPpinfty`, `ereal_cvgPninfty`, `ereal_squeeze`, `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`, `ereal_cvgD_pinfty_pinfty`, `ereal_cvgD_ninfty_ninfty`, `ereal_cvgD`, `ereal_cvgB`, `ereal_is_cvgD`, `ereal_cvg_sub0`, `ereal_limD`, `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`, `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`, `ereal_lim_sum`, `elim_inf_shift`, `elim_sup_le_cvg`, `elim_infN`, `elim_supN`, `elim_inf_sup`, `cvg_ninfty_elim_inf_sup`, `cvg_ninfty_einfs`, `cvg_ninfty_esups`, `cvg_pinfty_einfs`, `cvg_pinfty_esups`, `cvg_elim_inf_sup`, `is_cvg_elim_infE`, and `is_cvg_elim_supE`.
- in file `topology.v`
  + removed lemmas `cvg_map_lim`, `cvg_ballPpos`, and `app_cvg_locally`.

### Potentially changed

`pred_oappE`, `pred_oapp_set`, `itvxx`, `itvxxP`, `subset_itv_oo_cc`, `gee0P`, `fin_num_abs`, `abse_fin_num`, `addye`, `addey`, `lee_opp2`, `lte_opp2`, `ereal_nbhs_pinfty_ge`, `ereal_nbhs_ninfty_le`, `fatou`, `nbhsN`, `nearN`, `pinfty_ex_gt`, `pinfty_ex_gt0`, `near_pinfty_div2`, `normrZV`, `nbhs_normP`, `nbhs_le_nbhs_norm`, `nbhs_norm_le_nbhs`, `nbhs_normE`, `filter_from_normE`, `near_nbhs_norm`, `nbhs0_lt`, `dnbhs0_lt`, `nbhs0_le`, `dnbhs0_le`, `nbhs_norm_ball`, `bound_side`, `open_lt`, `open_gt`, `open_neq`, `interval_open`, `closed_le`, `closed_ge`, `closed_eq`, `interval_closed`, `at_left`, `at_right`, `at_right_in_segment`, `self_sub`, `fun1`, `dominated_by`, `strictly_dominated_by`, `sub_dominatedl`, `sub_dominatedr`, `dominated_by1`, `strictly_dominated_by1`, `ex_dom_bound`, `ex_strict_dom_bound`, `cvg_bounded`, `opp_continuous`, `add_continuous`, `natmul_continuous`, `scale_continuous`, `scaler_continuous`, `scalel_continuous`, `cvgN`, `cvg_norm`, `is_cvg_norm`, `cvgV`, `is_cvgV`, `cvgM`, `is_cvgM`, `is_cvgMr`, `is_cvgMrE`, `is_cvgMl`, `is_cvgMlE`, `lim_norm`, `limV`, `lim_ge`, `lim_le`, `abse_continuous`, `cvg_abse`, `is_cvg_abse`, `mule_continuous`, `open_ereal_lt`, `open_ereal_gt`, `open_ereal_lt'`, `open_ereal_gt'`, `open_ereal_lt_ereal`, `open_ereal_gt_ereal`, `closed_ereal_le_ereal`, `closed_ereal_ge_ereal`, `closure_gt`, `closure_lt`, `is_interval`, `is_intervalPlt`, `interval_is_interval`, `nbhs_image_ERFin`, `nbhs_open_ereal_lt`, `nbhs_open_ereal_gt`, `nbhs_open_ereal_pinfty`, `nbhs_open_ereal_ninfty`, `ereal_hausdorff`, `EFin_lim`, `squeeze`, `ler_lim`, `lee_lim`, `linear_boundedP`, `le_bnd_ereal`, `lt_ereal_bnd`, `Interval_ereal_mem`, `ereal_mem_Interval`, `itv_cpinfty_pinfty`, `itv_opinfty_pinfty`, `itv_cninfty_pinfty`, `itv_oninfty_pinfty`, `contraction_dist`, `contraction_cvg`, `contraction_cvg_fixed`, `cvg_lim`, `lim_near_cst`, `lim_cst`, `cvg_ballP`, `cvg_ball`, and `cvg_ball2P`.

### Infrastructure

### Misc
