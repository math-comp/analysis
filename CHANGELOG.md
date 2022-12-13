# Changelog

Lastest releases: [[0.6.0] - 2022-12-14](#060---2022-12-14) and [[0.5.4] - 2022-09-07](#055---2022-09-07)

## [0.6.0] - 2022-12-14

### Added

- OPAM package `coq-mathcomp-classical` containing `boolp.v`
- file `all_classical.v`
- file `classical/set_interval.v`
- in `mathcomp_extra.v`
  + lemma `lez_abs2n`
  + lemmas `pred_oappE` and `pred_oapp_set` (from `classical_sets.v`)
  + lemma `sumr_le0`
  + new definition `inv_fun`.
  + new lemmas `ler_ltP`, and `real_ltr_distlC`.
  + new definitions `proj`, and `dfwith`.
  + new lemmas `dfwithin`, `dfwithout`, and `dfwithP`.
  + new lemma `projK`
  + generalize lemmas `bigmax_le`, `bigmax_lt`, `lt_bigmin` and
    `le_bigmin` from `finType` to `Type`
  + new definition `oAC` to turn an AC operator `T -> T -> T`,
    into a monoid com_law `option T -> option T -> option T`.
  + new generic lemmas `opACE`, `some_big_AC`, `big_ACE`, `big_undup_AC`,
    `perm_big_AC`, `sub_big`, `sub_big_seq`, `sub_big_seq_cond`,
    `uniq_sub_big`, `uniq_sub_big_cond`, `sub_big_idem`, `sub_big_idem_cond`,
    `sub_in_big`, `le_big_ord`, `subset_big`, `subset_big_cond`,
    `le_big_nat_cond`, `le_big_nat`, and `le_big_ord_cond`,
  + specialization to `bigmax`: `sub_bigmax`, `sub_bigmax_seq`,
    `sub_bigmax_cond`, `sub_in_bigmax`, `le_bigmax_nat`,
    `le_bigmax_nat_cond`, `le_bigmax_ord`, `le_bigmax_ord_cond`,
    `subset_bigmax`, and `subset_bigmax_cond`.
  + specialization to `bigmin`,  `sub_bigmax`, `sub_bigmin_seq`,
    `sub_bigmin_cond`, `sub_in_bigmin`, `le_bigmin_nat`,
    `le_bigmin_nat_cond`, `le_bigmin_ord`, `le_bigmin_ord_cond`,
    `subset_bigmin`, and `subset_bigmin_cond`.
- in `classical_sets.v`
  + lemmas `IIDn`, `IISl`
  + lemmas `set_compose_subset`, `compose_diag`
  + notation `\;` for the composition of relations
  + notations `\bigcup_(i < n) F` and `\bigcap_(i < n) F`
  + new lemmas `eq_image_id`, `subKimage`, `subimageK`, and `eq_imageK`.
  + lemma `bigsetU_sup`
  + lemma `image2_subset`
- in `constructive_ereal.v`
  + lemmas `fine_le`, `fine_lt`, `fine_abse`, `abse_fin_num`
  + lemmas `gte_addl`, `gte_addr`
  + lemmas `gte_daddl`, `gte_daddr`
  + lemma `lte_spadder`, `lte_spaddre`
  + lemma `lte_spdadder`
  + lemma `sum_fine`
  + lemmas `lteN10`, `leeN10`
  + lemmas `le0_fin_numE`
  + lemmas `fine_lt0`, `fine_le0`
  + lemma `fine_lt0E`
  + multi-rules `lteey`, `lteNye`
  + new lemmas `real_ltry`, `real_ltNyr`, `real_leey`, `real_leNye`,
    `fin_real`, `addNye`, `addeNy`, `gt0_muley`, `lt0_muley`, `gt0_muleNy`, and
    `lt0_muleNy`.
  + new lemmas `daddNye`, and `daddeNy`.
  + lemma `lt0e`
  + canonicals `maxe_monoid`, `maxe_comoid`, `mine_monoid`, `mine_comoid`
- in `functions.v`,
  + new lemmas `inv_oppr`, `preimageEoinv`, `preimageEinv`, and
    `inv_funK`.
- in `cardinality.v`
  + lemmas `eq_card1`, `card_set1`, `card_eqSP`, `countable_n_subset`,
     `countable_finite_subset`, `eq_card_fset_subset`, `fset_subset_countable`
- in `fsbigop.v`:
  + lemmas `fsumr_ge0`, `fsumr_le0`, `fsumr_gt0`, `fsumr_lt0`, `pfsumr_eq0`,
    `pair_fsbig`, `exchange_fsbig`
  + lemma `fsbig_setU_set1`
- in `ereal.v`:
  + notation `\sum_(_ \in _) _` (from `fsbigop.v`)
  + lemmas `fsume_ge0`, `fsume_le0`, `fsume_gt0`, `fsume_lt0`,
    `pfsume_eq0`, `lee_fsum_nneg_subset`, `lee_fsum`,
    `ge0_mule_fsumr`, `ge0_mule_fsuml` (from `fsbigop.v`)
  + lemmas `finite_supportNe`, `dual_fsumeE`, `dfsume_ge0`, `dfsume_le0`,
    `dfsume_gt0`, `dfsume_lt0`, `pdfsume_eq0`, `le0_mule_dfsumr`, `le0_mule_dfsuml`
  + lemma `fsumEFin`
  + new lemmas `ereal_nbhs_pinfty_gt`, `ereal_nbhs_ninfty_lt`,
    `ereal_nbhs_pinfty_real`, and `ereal_nbhs_ninfty_real`.
- in `classical/set_interval.v`:
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
- in `topology.v`:
  + lemmas `continuous_subspaceT`, `subspaceT_continuous`
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
  + lemmas `entourage_invI`, `split_ent_subset`
  + definition `countable_uniform_pseudoMetricType_mixin`
  + lemmas `closed_bigsetU`, `accessible_finite_set_closed`
  + new lemmas `eq_cvg`, `eq_is_cvg`, `eq_near`, `cvg_toP`, `cvgNpoint`,
    `filter_imply`, `nbhs_filter`, `near_fun`, `cvgnyPgt`, `cvgnyPgty`,
    `cvgnyPgey`, `fcvg_ballP`, `fcvg_ball`, and `fcvg_ball2P`.
  + new lemmas `dfwith_continuous`, and `proj_open`.
- in `topology.v`, added `near do` and `near=> x do` tactic notations
  to perform some tactics under a `\forall x \near F, ...` quantification.
- in `reals.v`:
  + lemma `floor0`
- in `normedtype.v`,
  + lemmas `closed_ballR_compact` and `locally_compactR`
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
    `cvgr_norm_geNy`, `fcvgr2dist_ltP`, `cvgr2dist_ltP`, `cvgr2dist_lt`,
    `cvgNP`, `norm_cvg0P`, `cvgVP`, `is_cvgVE`, `cvgr_to_ge`, `cvgr_to_le`,
    `nbhs_EFin`, `nbhs_ereal_pinfty`, `nbhs_ereal_ninfty`, `fine_fcvg`,
    `fcvg_is_fine`, `fine_cvg`, `cvg_is_fine`, `cvg_EFin`, `neq0_fine_cvgP`,
    `cvgeNP`, `is_cvgeNE`, `cvge_to_ge`, `cvge_to_le`, `is_cvgeM`, `limeM`,
    `cvge_ge`, `cvge_le`, `lim_nnesum`, `ltr0_cvgV0`, `cvgrVNy`, `ler_cvg_to`,
    `gee_cvgy`, `lee_cvgNy`, `squeeze_fin`, and `lee_cvg_to`.
- in `normedtype.v`, added notations `^'+`, `^'-`, `+oo_R`, `-oo_R`
- in `sequences.v`,
  + lemma `invr_cvg0` and `invr_cvg_pinfty`
  + lemma `cvgPninfty_lt`, `cvgPpinfty_near`, `cvgPninfty_near`,
    `cvgPpinfty_lt_near` and `cvgPninfty_lt_near`
  + new lemma `nneseries_pinfty`.
  + lemmas `is_cvg_ereal_npos_natsum_cond`, `lee_npeseries`,
    `is_cvg_npeseries_cond`, `is_cvg_npeseries`, `npeseries_le0`,
    `is_cvg_ereal_npos_natsum`
  + lemma `nnseries_is_cvg`
- in `measure.v`:
  + definition `discrete_measurable_bool` with an instance of measurable type
  + lemmas `measurable_fun_if`, `measurable_fun_ifT`
  + lemma `measurable_fun_bool`
- in `lebesgue_measure.v`:
  + definition `ErealGenInftyO.R` and lemma `ErealGenInftyO.measurableE`
  + lemma `sub1set`
- in `lebesgue_integral.v`:
  + lemma `integral_cstNy`
  + lemma `ae_eq0`
  + lemma `integral_cst`
  + lemma `le_integral_comp_abse`
  + lemmas `integral_fune_lt_pinfty`, `integral_fune_fin_num`
  + lemmas `emeasurable_fun_fsum`, `ge0_integral_fsum`

### Changed

- in `constructive_ereal.v`:
  + lemmas `lee_paddl`, `lte_paddl`, `lee_paddr`, `lte_paddr`,
    `lte_spaddr`, `lee_pdaddl`, `lte_pdaddl`, `lee_pdaddr`,
    `lte_pdaddr`, `lte_spdaddr` generalized to `realDomainType`
  + generalize `lte_addl`, `lte_addr`, `gte_subl`, `gte_subr`,
    `lte_daddl`, `lte_daddr`, `gte_dsubl`, `gte_dsubr`
- in `topology.v`
  + definition `fct_restrictedUniformType` changed to use `weak_uniformType`
  + definition `family_cvg_topologicalType` changed to use `sup_uniformType`
  + lemmas `continuous_subspace0`, `continuous_subspace1`
- in `realfun.v`:
  + Instance for `GRing.opp` over real intervals
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
- in `sequence.v`:
  + `nneseries_pinfty` generalized to `eseries_pinfty`
- in `measure.v`:
  + `covered_by_countable` generalized from `pointedType` to `choiceType`
- in `lebesgue_measure.v`:
  + definition `fimfunE` now uses fsbig
  + generalize and rename `eitv_c_infty` to `eitv_bnd_infty` and
    `eitv_infty_c` to `eitv_infty_bnd`
  + generalize `ErealGenOInfty.G`, `ErealGenCInfty.G`, `ErealGenInftyO.G`
- in `lebesgue_integral.v`:
  + implicits of `ae_eq_integral`
- moved from `mathcomp_extra.v` to `classical_sets.v`: `pred_oappE`, and
    `pred_oapp_set`.
- moved from `normedtype.v` to `mathcomp_extra.v`: `itvxx`, `itvxxP`,
    `subset_itv_oo_cc`, and `bound_side`.
- moved from `sequences.v` to `normedtype.v`: `ler_lim`.
- `sub_dominatedl` and `sub_dominatedr` generalized from
  `numFieldType` to `numDomainType`.
- `abse_fin_num` changed from an equivalence to an equality.
- `lee_opp2` and `lte_opp2` generalized from `realDomainType` to
  `numDomainType`.
- `cvgN`, `cvg_norm`, `is_cvg_norm` generalized from
  `normedModType`/`topologicalType` to
  `pseudoMetricNormedZmodType`/`Type`
- `cvgV`, `is_cvgV`, `cvgM`, `is_cvgM`, `is_cvgMr`, `is_cvgMl`,
  `is_cvgMrE`, `is_cvgMlE`, `limV`, `cvg_abse`, `is_cvg_abse`
  generalized from `TopologicalType` to `Type`
- `lim_norm` generalized from `normedModType`/`TopoligicalType` to
  `pseudoMetricNormedZmodType`/`Type`
- updated `cvg_ballP`, `cvg_ball2P`, `cvg_ball`, and `cvgi_ballP` to
  match a `f @ F` instead of just an `F`. The old lemmas are still
  available with prefix `f`.
- generalized `lee_lim` to any proper filter and moved from
  `sequences.v` to `normedtype.v`.
- generalized `ereal_nbhs_pinfty_ge` and `ereal_nbhs_ninfty_le`.
- renamed `nbhsN` to `nbhsNimage`  and `nbhsN` is now replaced by
  `nbhs (- x) = -%R @ x`
- fixed the statements of `nbhs_normP` which used to be an accidental
  alias of `nbhs_ballP` together with `nbhs_normE`,
  `nbhs_le_nbhs_norm`, `nbhs_norm_le_nbhs`, `near_nbhs_norm` and
  `nbhs_norm_ball` which were not about `nbhs_ball_ ball_norm` but
  should have been.
- `EFin_lim` generalized from `realType` to `realFieldType`

### Renamed

- file `theories/mathcomp_extra.v` moved to `classical/mathcomp_extra.v`
- file `theories/boolp.v` -> `classical/boolp.v`
- file `theories/classical_sets.v` -> `classical/classical_sets.v`
- file `theories/functions.v` -> `classical/functions.v`
- file `theories/cardinality.v` -> `classical/cardinality.v`
- file `theories/fsbigop.v` -> `classical/fsbigop.v`
- file `theories/set_interval.v` -> `theories/real_interval.v`
- in `mathcomp_extra.v`:
  + `homo_le_bigmax` -> `le_bigmax2`
- in `constructive_ereal.v`:
  + `lte_spdaddr` -> `lte_spdaddre`
  + `esum_ninftyP` -> `esum_eqNyP`
  + `esum_ninfty` -> `esum_eqNy`
  + `esum_pinftyP` -> `esum_eqyP`
  + `esum_pinfty` -> `esum_eqy`
  + `desum_pinftyP` -> `desum_eqyP`
  + `desum_pinfty` -> `desum_eqy`
  + `desum_ninftyP` -> `desum_eqNyP`
  + `desum_ninfty` -> `desum_eqNy`
  + `eq_pinftyP` -> `eqyP`
  + `ltey` -> `ltry`
  + `ltNye` -> `ltNyr`
- in `topology.v`:
  + renamed `continuous_subspaceT` to `continuous_in_subspaceT`
  + `pasting` -> `withinU_continuous`
  + `cvg_map_lim` -> `cvg_lim`
  + `cvgi_map_lim` -> `cvgi_lim`
  + `app_cvg_locally` -> `cvg_ball`
  + `prod_topo_apply_continuous` -> `proj_continuous`
- in `normedtype.v`,
  + `normmZ` -> `normrZ`
  + `norm_cvgi_map_lim` -> `norm_cvgi_lim`
  + `nbhs_image_ERFin` -> `nbhs_image_EFin`
- moved from `sequences.v` to `normedtype.v`:
  + `squeeze` -> `squeeze_cvgr`
- in `sequences.v`:
  + `nneseries0` -> `eseries0`
  + `nneseries_pred0` -> `eseries_pred0`
  + `eq_nneseries` -> `eq_eseries`
  + `nneseries_mkcond` -> `eseries_mkcond`
  + `seqDUE` -> `seqDU_seqD`
  + `elim_sup` -> `lim_esup`
  + `elim_inf` -> `lim_einf`
  + `elim_inf_shift` -> `lim_einf_shift`
  + `elim_sup_le_cvg` -> `lim_esup_le_cvg`
  + `elim_infN` -> `lim_einfN`
  + `elim_supN` -> `lim_esupN`
  + `elim_inf_sup` -> `lim_einf_sup`
  + `cvg_ninfty_elim_inf_sup` -> `cvgNy_lim_einf_sup`
  + `cvg_ninfty_einfs` -> `cvgNy_einfs`
  + `cvg_ninfty_esups` -> `cvgNy_esups`
  + `cvg_pinfty_einfs` -> `cvgy_einfs`
  + `cvg_pinfty_esups` -> `cvgy_esups`
  + `cvg_elim_inf_sup` -> `cvg_lim_einf_sup`
  + `is_cvg_elim_infE` -> `is_cvg_lim_einfE`
  + `is_cvg_elim_supE` -> `is_cvg_lim_esupE`
- in `measure.v`,
  + `caratheodory_lim_lee` -> `caratheodory_lime_le`
- in `lebesgue_measure.v`,
  + `measurable_fun_elim_sup` -> `measurable_fun_lim_esup`
- moved from `lebesgue_measure.v` to `real_interval.v`:
  + `itv_cpinfty_pinfty` -> `itv_cyy`
  + `itv_opinfty_pinfty` -> `itv_oyy`
  + `itv_cninfty_pinfty` -> `itv_cNyy`
  + `itv_oninfty_pinfty` -> `itv_oNyy`
- in `lebesgue_integral.v`:
  + `integral_cst_pinfty` -> `integral_csty`
  + `sintegral_cst` -> `sintegral_EFin_cst`
  + `integral_cst` -> `integral_cstr`

### Generalized

- in `constructive_ereal.v`,
  + `daddooe` -> `daddye`
  + `daddeoo` -> `daddey`
  + `ltey`, `ltNye`
- moved from `normedtype.v` to `mathcomp_extra.v`:
  + `ler0_addgt0P` -> `ler_gtP`
- in `normedtype.v`,
  + `cvg_gt_ge` -> `cvgr_ge`
  + `cvg_lt_le` -> `cvgr_le`
  + `cvg_dist0` -> `norm_cvg0`
  + `ereal_cvgN` -> `cvgeN`
  + `ereal_is_cvgN` -> `is_cvgeN`
  + `ereal_cvgrM` -> `cvgeMl`
  + `ereal_is_cvgrM` -> `is_cvgeMl`
  + `ereal_cvgMr` -> `cvgeMr`
  + `ereal_is_cvgMr` -> `is_cvgeMr`
  + `ereal_limrM` -> `limeMl`
  + `ereal_limMr` -> `limeMr`
  + `ereal_limN` -> `limeN`
  + `linear_continuous0` -> `continuous_linear_bounded`
  + `linear_bounded0` -> `bounded_linear_continuous`
- moved from `derive.v` to `normedtype.v`:
  + `le0r_cvg_map` -> `limr_ge`
  + `ler0_cvg_map` -> `limr_le`
- moved from `sequences.v` to `normedtype.v`:
  + `ereal_cvgM` -> `cvgeM`
  + `cvgPpinfty` -> `cvgryPge`
  + `cvgPninfty` -> `cvgrNyPle`
  + `ger_cvg_pinfty` -> `ger_cvgy`
  + `ler_cvg_ninfty` -> `ler_cvgNy`
  + `cvgPpinfty_lt` -> `cvgryPgt`
  + `cvgPninfty_lt` -> `cvgrNyPlt`
  + `cvgPpinfty_near` -> `cvgryPgey`
  + `cvgPninfty_near` -> `cvgrNyPleNy`
  + `cvgPpinfty_lt_near` -> `cvgryPgty`
  + `cvgPninfty_lt_near` -> `cvgrNyPltNy`
  + `invr_cvg0` -> `gtr0_cvgV0`
  + `invr_cvg_pinfty` -> `cvgrVy`
  + `nat_dvg_real` -> `cvgrnyP`
  + `ereal_cvg_abs0` -> `cvg_abse0P`
  + `ereal_lim_ge` -> `lime_ge`
  + `ereal_lim_le` -> `lime_le`
  + `dvg_ereal_cvg` -> `cvgeryP`
  + `ereal_cvg_real` -> `fine_cvgP`
  + `ereal_squeeze` -> `squeeze_cvge`
  + `ereal_cvgD` -> `cvgeD`
  + `ereal_cvgB` -> `cvgeB`
  + `ereal_is_cvgD` -> `is_cvgeD`
  + `ereal_cvg_sub0` -> `cvge_sub0`
  + `ereal_limD` -> `limeD`
  + `ereal_lim_sum` -> `cvg_nnesum`
- moved from `sequences.v` to `topology.v`:
  + `nat_cvgPpinfty` -> `cvgnyPge`
- in `topology.v`
  + `prod_topo_apply` -> `proj`
- in `lebesgue_integral.v`:
  + `integral_sum` -> `integral_nneseries`

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr`, renamed `lte_spaddre`
- in `topology.v`, deprecated
  + `cvg_ballPpos` (use a combination of `cvg_ballP` and `posnumP`),
  + `cvg_dist` (use `cvgr_dist_lt` or a variation instead)
- in `normedtype.v`, deprecated
  + `cvg_distP` (use `cvgrPdist_lt` or a variation instead),
  + `cvg_dist` (use `cvg_dist_lt` or a variation instead),
  + `cvg_distW` (use `cvgrPdist_le` or a variation instead),
  + `cvg_bounded_real` (use `cvgr_norm_lty` or a variation instead),
  + `continuous_cvg_dist` (simply use the fact that `(x --> l) -> (x = l)`),
  + `cvg_dist2P` (use `cvgr2dist_ltP` or a variant instead),
  + `cvg_dist2` (use `cvgr2dist_lt` or a variant instead),
- in `derive.v`, deprecated
  + `ler_cvg_map` (subsumed by `ler_lim`),
- in `sequences.v`, deprecated
  + `cvgNpinfty` (use `cvgNry` instead),
  + `cvgNninfty` (use `cvgNrNy` instead),
  + `ereal_cvg_ge0` (use `cvge_ge` instead),
  + `ereal_cvgPpinfty` (use `cvgeyPge` or a variant instead),
  + `ereal_cvgPninfty` (use `cvgeNyPle` or a variant instead),
  + `ereal_cvgD_pinfty_fin` (use `cvgeD` instead),
  + `ereal_cvgD_ninfty_fin` (use `cvgeD` instead),
  + `ereal_cvgD_pinfty_pinfty` (use `cvgeD` instead),
  + `ereal_cvgD_ninfty_ninfty` (use `cvgeD` instead),
  + `ereal_cvgM_gt0_pinfty` (use `cvgeM` instead),
  + `ereal_cvgM_lt0_pinfty` (use `cvgeM` instead),
  + `ereal_cvgM_gt0_ninfty` (use `cvgeM` instead),
  + `ereal_cvgM_lt0_ninfty` (use `cvgeM` instead),

### Removed

- in `classical_sets.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (moved to `mathcomp_extra.v`)
- in `fsbigop.v`:
  + notation `\sum_(_ \in _) _` (moved to `ereal.v`)
  + lemma `lee_fsum_nneg_subset`, `lee_fsum`, `ge0_mule_fsumr`,
    `ge0_mule_fsuml`, `fsume_ge0`, `fsume_le0`, `fsume_gt0`,
    `fsume_lt0`, `pfsume_eq0` (moved to `ereal.v`)
  + lemma `pair_fsum` (subsumed by `pair_fsbig`)
  + lemma `exchange_fsum` (subsumed by `exchange_fsbig`)
- in `reals.v`:
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (moved to `classical/set_interval.v`)
- in `set_interval.v`:
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
- in `topology.v`
  + lemmas `prod_topo_applyE`

## [0.5.4] - 2022-09-07

### Added

- in `mathcomp_extra.v`:
  + defintion `onem` and notation ``` `1- ```
  + lemmas `onem0`, `onem1`, `onemK`, `onem_gt0`, `onem_ge0`, `onem_le1`, `onem_lt1`,
    `onemX_ge0`, `onemX_lt1`, `onemD`, `onemMr`, `onemM`
  + lemmas `natr1`, `nat1r`
- in `classical_sets.v`:
  + lemmas `subset_fst_set`, `subset_snd_set`, `fst_set_fst`, `snd_set_snd`,
    `fset_setM`, `snd_setM`, `fst_setMR`
  + lemmas `xsection_snd_set`, `ysection_fst_set`
- in `constructive_ereal.v`:
  + lemmas `ltNye_eq`, `sube_lt0`, `subre_lt0`, `suber_lt0`, `sube_ge0`
  + lemmas `dsubre_gt0`, `dsuber_gt0`, `dsube_gt0`, `dsube_le0`
- in `signed.v`:
  + lemmas `onem_PosNum`, `onemX_NngNum`
- in `fsbigop.v`:
  + lemmas `lee_fsum_nneg_subset`, `lee_fsum`
- in `topology.v`:
  + lemma `near_inftyS`
  + lemma `continuous_closedP`, `closedU`, `pasting`
  + lemma `continuous_inP`
  + lemmas `open_setIS`, `open_setSI`, `closed_setIS`, `closed_setSI`
- in `normedtype.v`:
  + definitions `contraction` and `is_contraction`
  + lemma `contraction_fixpoint_unique`
- in `sequences.v`:
  + lemmas `contraction_dist`, `contraction_cvg`,
    `contraction_cvg_fixed`, `banach_fixed_point`,
    `contraction_unique`
- in `derive.v`:
  + lemma `diff_derivable`
- in `measure.v`:
  + lemma `measurable_funTS`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_fine`
  + lemma `open_measurable_subspace`
  + lemma ``subspace_continuous_measurable_fun``
  + corollary `open_continuous_measurable_fun`
  + Hint about `measurable_fun_normr`
- in `lebesgue_integral.v`:
  + lemma `measurable_fun_indic`
  + lemma `ge0_integral_mscale`
  + lemma `integral_pushforward`

### Changed

- in `esum.v`:
  + definition `esum`
- moved from `lebesgue_integral.v` to `classical_sets.v`:
  + `mem_set_pair1` -> `mem_xsection`
  + `mem_set_pair2` -> `mem_ysection`
- in `derive.v`:
  + generalized `is_diff_scalel`
- in `measure.v`:
  + generalize `measurable_uncurry`
- in `lebesgue_measure.v`:
  + `pushforward` requires a proof that its argument is measurable
- in `lebesgue_integral.v`:
  + change implicits of `integralM_indic`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pinfty_eq` -> `ltey_eq`
  + `le0R` -> `fine_ge0`
  + `lt0R` -> `fine_gt0`
- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `esum.v`:
  + `esum0` -> `esum1`
- in `sequences.v`:
  + `nneseries_lim_ge0` -> `nneseries_ge0`
- in `measure.v`:
  + `ring_fsets` -> `ring_finite_set`
  + `discrete_measurable` -> `discrete_measurable_nat`
  + `cvg_mu_inc` -> `nondecreasing_cvg_mu`
- in `lebesgue_integral.v`:
  + `muleindic_ge0` -> `nnfun_muleindic_ge0`
  + `mulem_ge0` -> `mulemu_ge0`
  + `nnfun_mulem_ge0` -> `nnsfun_mulemu_ge0`

### Removed

- in `esum.v`:
  + lemma `fsetsP`, `sum_fset_set`

## [0.5.3] - 2022-08-10

### Added

- in `mathcomp_extra.v`:
  + lemma `big_const_idem`
  + lemma `big_id_idem`
  + lemma `big_rem_AC`
  + lemma `bigD1_AC`
  + lemma `big_mkcond_idem`
  + lemma `big_split_idem`
  + lemma `big_id_idem_AC`
  + lemma `bigID_idem`
  + lemmas `bigmax_le` and `bigmax_lt`
  + lemma `bigmin_idr`
  + lemma `bigmax_idr`
- in file `boolp.v`:
  + lemmas `iter_compl`, `iter_compr`, `iter0`
- in file `functions.v`:
  + lemmas `oinv_iter`, `some_iter_inv`, `inv_iter`,
  + Instances for functions interfaces for `iter` (partial inverse up to
      bijective function)
- in `classical_sets.v`:
  + lemma `preimage10P`
  + lemma `setT_unit`
  + lemma `subset_refl`
- in `ereal.v`:
  + notations `_ < _ :> _` and `_ <= _ :> _`
  + lemmas `lee01`, `lte01`, `lee0N1`, `lte0N1`
  + lemmas `lee_pmul2l`, `lee_pmul2r`, `lte_pmul`, `lee_wpmul2l`
  + lemmas `lee_lt_add`, `lee_lt_dadd`, `lee_paddl`, `lee_pdaddl`,
    `lte_paddl`, `lte_pdaddl`, `lee_paddr`, `lee_pdaddr`,
    `lte_paddr`, `lte_pdaddr`
  + lemmas `muleCA`, `muleAC`, `muleACA`
- in `reals.v`:
  + lemmas `Rfloor_lt_int`, `floor_lt_int`, `floor_ge_int`
  + lemmas `ceil_ge_int`, `ceil_lt_int`
- in `lebesgue_integral.v`:
  + lemma `ge0_emeasurable_fun_sum`
  + lemma `integrableMr`

### Changed

- in `ereal.v`:
  + generalize `lee_pmul`
  + simplify `lte_le_add`, `lte_le_dadd`, `lte_le_sub`, `lte_le_dsub`
- in `measure.v`:
  + generalize `pushforward`
- in `lebesgue_integral.v`
  + change `Arguments` of `eq_integrable`
  + fix pretty-printing of `{mfun _ >-> _}`, `{sfun _ >-> _}`, `{nnfun _ >-> _}`
  + minor generalization of `eq_measure_integral`
- from `topology.v` to `mathcomp_extra.v`:
  + generalize `ltr_bigminr` to `porderType` and rename to `bigmin_lt`
  + generalize `bigminr_ler` to `orderType` and rename to `bigmin_le`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v`
  and generalized to `orderType`:
  + lemma `bigminr_ler_cond`, renamed to `bigmin_le_cond`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v`:
  + lemma `bigminr_maxr`
- moved from from module `Bigminr` in `normedtype.v`
  + to `mathcomp_extra.v` and generalized to `orderType`
    * `bigminr_mkcond` -> `bigmin_mkcond`
    * `bigminr_split` -> `bigmin_split`
    * `bigminr_idl` -> `bigmin_idl`
    * `bigminrID` -> `bigminID`
    * `bigminrD1` -> `bigminD1`
    * `bigminr_inf` -> `bigmin_inf`
    * `bigminr_gerP` -> `bigmin_geP`
    * `bigminr_gtrP` -> ``bigmin_gtP``
    * `bigminr_eq_arg` -> `bigmin_eq_arg`
    * `eq_bigminr` -> `eq_bigmin`
  + to `topology.v` and generalized to `orderType`
    * `bigminr_lerP` -> `bigmin_leP`
    * `bigminr_ltrP` -> `bigmin_ltP`
- moved from `topology.v` to `mathcomp_extra.v`:
  + `bigmax_lerP` -> `bigmax_leP`
  + `bigmax_ltrP` -> `bigmax_ltP`
  + `ler_bigmax_cond` -> `le_bigmax_cond`
  + `ler_bigmax` -> `le_bigmax`
  + `le_bigmax` -> `homo_le_bigmax`

### Renamed

- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `classical_sets.v`:
  + `set_bool` -> `setT_bool`
- in `topology.v`:
  + `bigmax_gerP` -> `bigmax_geP`
  + `bigmax_gtrP` -> `bigmax_gtP`
- in `lebesgue_integral.v`:
  + `emeasurable_funeM` -> `measurable_funeM`

### Removed

- in `topology.v`:
  + `bigmax_seq1`, `bigmax_pred1_eq`, `bigmax_pred1`
- in `normedtype.v` (module `Bigminr`)
  + `bigminr_ler_cond`, `bigminr_ler`.
  + `bigminr_seq1`, `bigminr_pred1_eq`, `bigminr_pred1`

### Misc

- file `ereal.v` split in two files `constructive_ereal.v` and
  `ereal.v` (the latter exports the former, so the "Require Import
  ereal" can just be kept unchanged)

## [0.5.2] - 2022-07-08

### Added

- in file `classical_sets.v`
  + lemma `set_bool`
  + lemma `supremum_out`
  + definition `isLub`
  + lemma `supremum1`
  + lemma `trivIset_set0`
  + lemmas `trivIset_image`, `trivIset_comp`
  + notation `trivIsets`
- in file `topology.v`:
  + definition `near_covering`
  + lemma `compact_near_coveringP`
  + lemma `continuous_localP`, `equicontinuous_subset_id`
  + lemmas `precompact_pointwise_precompact`, `precompact_equicontinuous`,
    `Ascoli`
  + definition `frechet_filter`, instances `frechet_properfilter`, and `frechet_properfilter_nat`
  + definition `principal_filter` `discrete_space`
  + lemma `principal_filterP`, `principal_filter_proper`,
      `principal_filter_ultra`
  + canonical `bool_discrete_filter`
  + lemma `compactU`
  + lemma `discrete_sing`, `discrete_nbhs`, `discrete_open`, `discrete_set1`,
      `discrete_closed`, `discrete_cvg`, `discrete_hausdorff`
  + canonical `bool_discrete_topology`
  + definition `discrete_topological_mixin`
  + lemma `discrete_bool`, `bool_compact`
- in `Rstruct.v`:
  + lemmas `Rsupremums_neq0`, `Rsup_isLub`, `Rsup_ub`
- in `reals.v`:
  + lemma `floor_natz`
  + lemma `opp_set_eq0`, `ubound0`, `lboundT`
- in file `lebesgue_integral.v`:
  + lemma `integrable0`
  + mixins `isAdditiveMeasure`, `isMeasure0`, `isMeasure`, `isOuterMeasure`
  + structures `AdditiveMeasure`, `Measure`, `OuterMeasure`
  + notations `additive_measure`, `measure`, `outer_measure`
  + definition `mrestr`
  + lemmas `integral_measure_sum_nnsfun`, `integral_measure_add_nnsfun`
  + lemmas `ge0_integral_measure_sum`, `integral_measure_add`, `integral_measure_series_nnsfun`,
    `ge0_integral_measure_series`
  + lemmas `integrable_neg_fin_num`, `integrable_pos_fin_num`
  + lemma `integral_measure_series`
  + lemmas `counting_dirac`, `summable_integral_dirac`, `integral_count`
  + lemmas `integrable_abse`, `integrable_summable`, `integral_bigcup`
- in `measure.v`:
  + lemmas `additive_measure_snum_subproof`, `measure_snum_subproof`
  + canonicals `additive_measure_snum`, `measure_snum`
  + definition `mscale`
  + definition `restr`
  + definition `counting`, canonical `measure_counting`
  + definition `discrete_measurable`, instantiated as a `measurableType`
  + lemma `sigma_finite_counting`
  + lemma `msum_mzero`
- in `lebesgue_measure.v`:
  + lemma `diracE`
  + notation `_.-ocitv`
  + definition `ocitv_display`
- in file `cardinality.v`:
  + lemmas `trivIset_sum_card`, `fset_set_sub`, `fset_set_set0`
- in file `sequences.v`:
  + lemmas `nat_dvg_real`, `nat_cvgPpinfty`, `nat_nondecreasing_is_cvg`
  + definition `nseries`, lemmas `le_nseries`, `cvg_nseries_near`, `dvg_nseries`
- in file `ereal.v`:
  + lemma `fin_num_abs`
- in file `esum.v`:
  + definition `summable`
  + lemmas `summable_pinfty`, `summableE`, `summableD`, `summableN`, `summableB`,
    `summable_funepos`, `summable_funeneg`
  + lemmas `summable_fine_sum`, `summable_cvg`, `summable_nneseries_lim`,
    `summable_nnseries`, `summable_nneseries_esum`, `esumB`
  + lemma `fsbig_esum`
- in `trigo.v`:
  + lemmas `cos1_gt0`, `pi_ge2`
  + lemmas `pihalf_ge1`, `pihalf_lt2`
- in `measure.v`:
  + inductive `measure_display`
  + notation `_.-sigma`, `_.-sigma.-measurable`,
             `_.-ring`, `_.-ring.-measurable`,
             `_.-cara`, `_.-cara.-measurable`,
             `_.-caratheodory`,
             `_.-prod`. `_.-prod.-measurable`
  + notation `_.-measurable`
  + lemma `measure_semi_additive_ord`, `measure_semi_additive_ord_I`
  + lemma `decomp_finite_set`
- in `functions.v`:
  + lemma `patch_pred`, `trivIset_restr`
- `has_sup1`, `has_inf1` moved from `reals.v` to `classical_sets.v`

### Changed

- in `topology.v`:
  + generalize `cluster_cvgE`, `fam_cvgE`, `ptws_cvg_compact_family`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index
- in `Rstruct.v`:
  + statement of lemma `completeness'`, renamed to `Rcondcomplete`
  + statement of lemma `real_sup_adherent`
- in `ereal.v`:
  + statements of lemmas `ub_ereal_sup_adherent`, `lb_ereal_inf_adherent`
- in `reals.v`:
  + definition `sup`
  + statements of lemmas `sup_adherent`, `inf_adherent`
- in `sequences.v`:
  + generalize `eq_nneseries`, `nneseries0`
- in `mathcomp_extra.v`:
  + generalize `card_fset_sum1`
- in `lebesgue_integral.v`:
  + change the notation `\int_`
  + `product_measure1` takes a proof that the second measure is sigma-finite
  + `product_measure2` takes a proof that the first measure is sigma-finite
  + definitions `integral` and `integrable` now take a function instead of a measure
  + remove one space in notation `\d_`
  + generalize `nondecreasing_series`
  + constant `measurableType` now take an addititional parameter of type `measure_display`
- in `measure.v`:
  + `measure0` is now a lemma
  + statement of lemmas `content_fin_bigcup`, `measure_fin_bigcup`, `ring_fsets`,
    `decomp_triv`, `cover_decomp`, `decomp_set0`, `decompN0`, `Rmu_fin_bigcup`
  + definitions `decomp`, `measure`
  + several constants now take a parameter of type `measure_display`
- in `trigo.v`:
  + lemma `cos_exists`
- in `set_interval.v`:
  + generalize to numDomainType:
    * `mem_1B_itvcc`, `conv`, `conv_id`, `convEl`, `convEr`,
    `conv10`, `conv0`, `conv1`, `conv_sym`, `conv_flat`, `leW_conv`,
    `factor`, `leW_factor`, `factor_flat`, `factorl`, `ndconv`,
    `ndconvE`
  + generalize to numFieldType
    * `factorr`, `factorK`, `convK`, `conv_inj`, `factor_inj`,
    `conv_bij`, `factor_bij`, `le_conv`, `le_factor`, `lt_conv`,
    `lt_factor`, `conv_itv_bij`, `factor_itv_bij`, `mem_conv_itv`,
    `mem_conv_itvcc`, `range_conv`, `range_factor`
  + generalize to realFieldType:
    * `mem_factor_itv`
- in `fsbig.v`:
  + generalize `exchange_fsum`
- lemma `preimage_cst` generalized and moved from `lebesgue_integral.v`
  to `functions.v`
- lemma `fset_set_image` moved from `measure.v` to `cardinality.v`
- in `reals.v`:
  + type generalization of `has_supPn`

### Renamed

- in `lebesgue_integral.v`:
  + `integralK` -> `integralrM`
- in `trigo.v`:
  + `cos_pihalf_uniq` -> `cos_02_uniq`
- in `measure.v`:
  + `sigma_algebraD` -> `sigma_algebraCD`
  + `g_measurable` -> `salgebraType`
  + `g_measurable_eqType` -> `salgebraType_eqType`
  + `g_measurable_choiceType` -> `salgebraType_choiceType`
  + `g_measurable_ptType` -> `salgebraType_ptType`
- in `lebesgue_measure.v`:
  + `itvs` -> `ocitv_type`
  + `measurable_fun_sum` -> `emeasurable_fun_sum`
- in `classical_sets.v`:
  + `trivIset_restr` -> `trivIset_widen`
  + `supremums_set1` -> `supremums1`
  + `infimums_set1` -> `infimums1`

### Removed

- in `Rstruct.v`:
  + definition `real_sup`
  + lemma `real_sup_is_lub`, `real_sup_ub`, `real_sup_out`
- in `reals.v`:
  + field `sup` from `mixin_of` in module `Real`
- in `measure.v`:
  + notations `[additive_measure _ -> _]`, `[measure _ -> _]`, `[outer_measure _ -> _ ]`,
  + lemma `measure_is_additive_measure`
  + definitions `caratheodory_measure_mixin`, `caratheodory_measure`
  + coercions `measure_to_nadditive_measure`, `measure_additive_measure`
  + canonicals `measure_additive_measure`, `set_ring_measure`,
    `outer_measure_of_measure`, `Hahn_ext_measure`
  + lemma `Rmu0`
  + lemma `measure_restrE`
- in `measure.v`:
  + definition `g_measurableType`
  + notation `mu.-measurable`

## [0.5.1] - 2022-06-04

### Added

- in `mathcomp_extra.v`:
  + lemma `card_fset_sum1`
- in `classical_sets.v`:
  + lemma `preimage_setT`
  + lemma `bigsetU_bigcup`
  + lemmas `setI_II` and `setU_II`
- in `topology.v`:
  + definition `powerset_filter_from`
  + globals `powerset_filter_from_filter`
  + lemmas `near_small_set`, `small_set_sub`
  + lemmas `withinET`, `closureEcvg`, `entourage_sym`, `fam_nbhs`
  + generalize `cluster_cvgE`, `ptws_cvg_compact_family`
  + lemma `near_compact_covering`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index
  + lemmas `ptws_cvg_entourage`, `equicontinuous_closure`, `ptws_compact_cvg`
    `ptws_compact_closed`, `ascoli_forward`, `compact_equicontinuous`
- in `normedtype.v`:
  + definition `bigcup_ointsub`
  + lemmas `bigcup_ointsub0`, `open_bigcup_ointsub`, `is_interval_bigcup_ointsub`,
    `bigcup_ointsub_sub`, `open_bigcup_rat`
  + lemmas `mulrl_continuous` and `mulrr_continuous`.
- in `ereal.v`:
  + definition `expe` with notation `^+`
  + definition `enatmul` with notation `*+` (scope `%E`)
  + definition `ednatmul` with notation `*+` (scope `%dE`)
  + lemmas `fineM`, `enatmul_pinfty`, `enatmul_ninfty`, `EFin_natmul`, `mule2n`, `expe2`,
    `mule_natl`
  + lemmas `ednatmul_pinfty`, `ednatmul_ninfty`, `EFin_dnatmul`, `dmule2n`, `ednatmulE`,
    `dmule_natl`
  + lemmas `sum_fin_num`, `sum_fin_numP`
  + lemmas `oppeB`, `doppeB`, `fineB`, `dfineB`
  + lemma `abse1`
  + lemma `ltninfty_adde_def`
- in `esum.v`:
  + lemma `esum_set1`
  + lemma `nnseries_interchange`
- in `cardinality.v`:
  + lemma `fset_set_image`, `card_fset_set`, `geq_card_fset_set`,
    `leq_card_fset_set`, `infinite_set_fset`, `infinite_set_fsetP` and
    `fcard_eq`.
- in `sequences.v`:
  + lemmas `nneseriesrM`, `ereal_series_cond`, `ereal_series`, `nneseries_split`
  + lemmas `lee_nneseries`
- in `numfun.v`:
  + lemma `restrict_lee`
- in `measure.v`:
  + definition `pushforward` and canonical `pushforward_measure`
  + definition `dirac` with notation `\d_` and canonical `dirac_measure`
  + lemmas `finite_card_dirac`, `infinite_card_dirac`
  + lemma `eq_measure`
  + definition `msum` and canonical `measure_sum'`
  + definition `mzero` and canonical `measure_zero'`
  + definition `measure_add` and lemma `measure_addE`
  + definition `mseries` and canonical `measure_series'`
- in `set_interval.v`:
  + lemma `opp_itv_infty_bnd`
- in `lebesgue_integral.v`:
  + lemmas `integral_set0`, `ge0_integral_bigsetU`, `ge0_integral_bigcup`
- in `lebesgue_measure.v`:
  + lemmas `is_interval_measurable`, `open_measurable`, `continuous_measurable_fun`
  + lemma `emeasurable_funN`
  + lemmas `itv_bnd_open_bigcup`, `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`,
    `itv_open_bnd_bigcup`
  + lemma `lebesgue_measure_set1`
  + lemma `lebesgue_measure_itv`
  + lemma `lebesgue_measure_rat`
- in `lebesgue_integral.v`:
  + lemmas `integralM_indic`, `integralM_indic_nnsfun`, `integral_dirac`
  + lemma `integral_measure_zero`
  + lemma `eq_measure_integral`

### Changed

- in `mathcomp_extra.v`:
  + generalize `card_fset_sum1`
- in `classical_sets.v`:
  + lemma `some_bigcup` generalized and renamed to `image_bigcup`
- in `esumv`:
  + remove one hypothesis in lemmas `reindex_esum`, `esum_image`
- moved from `lebesgue_integral.v` to `lebesgue_measure.v` and generalized
  + hint `measurable_set1`/`emeasurable_set1`
- in `sequences.v`:
  + generalize `eq_nneseries`, `nneseries0`
- in `set_interval.v`:
  + generalize `opp_itvoo` to `opp_itv_bnd_bnd`
- in `lebesgue_integral.v`:
  + change the notation `\int_`

### Renamed

- in `ereal.v`:
  + `num_abs_le` -> `num_abse_le`
  + `num_abs_lt` -> `num_abse_lt`
  + `addooe` -> `addye`
  + `addeoo` -> `addey`
  + `mule_ninfty_pinfty` -> `mulNyy`
  + `mule_pinfty_ninfty` -> `mulyNy`
  + `mule_pinfty_pinfty` -> `mulyy`
  + `mule_ninfty_ninfty` -> `mulNyNy`
  + `lte_0_pinfty` -> `lt0y`
  + `lte_ninfty_0` -> `ltNy0`
  + `lee_0_pinfty` -> `le0y`
  + `lee_ninfty_0` -> `leNy0`
  + `lte_pinfty` -> `ltey`
  + `lte_ninfty` -> `ltNye`
  + `lee_pinfty` -> `leey`
  + `lee_ninfty` -> `leNye`
  + `mulrpinfty_real` -> `real_mulry`
  + `mulpinftyr_real` -> `real_mulyr`
  + `mulrninfty_real` -> `real_mulrNy`
  + `mulninftyr_real` -> `real_mulNyr`
  + `mulrpinfty` -> `mulry`
  + `mulpinftyr` -> `mulyr`
  + `mulrninfty` -> `mulrNy`
  + `mulninftyr` -> `mulNyr`
  + `gt0_mulpinfty` -> `gt0_mulye`
  + `lt0_mulpinfty` -> `lt0_mulye`
  + `gt0_mulninfty` -> `gt0_mulNye`
  + `lt0_mulninfty` -> `lt0_mulNye`
  + `maxe_pinftyl` -> `maxye`
  + `maxe_pinftyr` -> `maxey`
  + `maxe_ninftyl` -> `maxNye`
  + `maxe_ninftyr` -> `maxeNy`
  + `mine_ninftyl` -> `minNye`
  + `mine_ninftyr` -> `mineNy`
  + `mine_pinftyl` -> `minye`
  + `mine_pinftyr` -> `miney`
  + `mulrinfty_real` -> `real_mulr_infty`
  + `mulrinfty` -> `mulr_infty`
- in `realfun.v`:
  + `exp_continuous` -> `exprn_continuous`
- in `sequences.v`:
  + `ereal_pseriesD` -> `nneseriesD`
  + `ereal_pseries0` -> `nneseries0`
  + `ereal_pseries_pred0` -> `nneseries_pred0`
  + `eq_ereal_pseries` -> `eq_nneseries`
  + `ereal_pseries_sum_nat` -> `nneseries_sum_nat`
  + `ereal_pseries_sum` -> `nneseries_sum`
  + `ereal_pseries_mkcond` -> `nneseries_mkcond`
  + `ereal_nneg_series_lim_ge` -> `nneseries_lim_ge`
  + `is_cvg_ereal_nneg_series_cond` -> `is_cvg_nneseries_cond`
  + `is_cvg_ereal_nneg_series` -> `is_cvg_nneseries`
  + `ereal_nneg_series_lim_ge0` -> `nneseries_lim_ge0`
  + `adde_def_nneg_series` -> `adde_def_nneseries`
- in `esum.v`:
  + `ereal_pseries_esum` -> `nneseries_esum`
- in `numfun.v`:
  + `funenng` -> `funepos`
  + `funennp` -> `funeneg`
  + `funenng_ge0` -> `funepos_ge0`
  + `funennp_ge0` -> `funeneg_ge0`
  + `funenngN` -> `funeposN`
  + `funennpN` -> `funenegN`
  + `funenng_restrict` -> `funepos_restrict`
  + `funennp_restrict` -> `funeneg_restrict`
  + `ge0_funenngE` -> `ge0_funeposE`
  + `ge0_funennpE` -> `ge0_funenegE`
  + `le0_funenngE` -> `le0_funeposE`
  + `le0_funennpE` -> `le0_funenegE`
  + `gt0_funenngM` -> `gt0_funeposM`
  + `gt0_funennpM` -> `gt0_funenegM`
  + `lt0_funenngM` -> `lt0_funeposM`
  + `lt0_funennpM` -> `lt0_funenegM`
  + `funenngnnp` -> `funeposneg`
  + `add_def_funennpg` -> `add_def_funeposneg`
  + `funeD_Dnng` -> `funeD_Dpos`
  + `funeD_nngD` -> `funeD_posD`
- in `lebesgue_measure.v`:
  + `emeasurable_fun_funenng` -> `emeasurable_fun_funepos`
  + `emeasurable_fun_funennp` -> `emeasurable_fun_funeneg`
- in `lebesgue_integral.v`:
  + `integrable_funenng` -> `integrable_funepos`
  + `integrable_funennp` -> `integrable_funeneg`
  + `integral_funennp_lt_pinfty` -> `integral_funeneg_lt_pinfty`
  + `integral_funenng_lt_pinfty` -> `integral_funepos_lt_pinfty`
  + `ae_eq_funenng_funennp` -> `ae_eq_funeposneg`

### Removed

- in `mathcomp_extra.v`:
  + lemmas `natr_absz`, `ge_pinfty`, `le_ninfty`, `gt_pinfty`,
    `lt_ninfty`
- in `classical_sets.v`:
  + notation `[set of _]`
- in `topology.v`:
  + lemmas `inj_can_sym_in_on`, `inj_can_sym_on`, `inj_can_sym_in`

## [0.5.0] - 2022-03-23

### Added

- in `signed.v`:
  + notations `%:nngnum` and `%:posnum`
- in `ereal.v`:
  + notations `{posnum \bar R}` and `{nonneg \bar R}`
  + notations `%:pos` and `%:nng` in `ereal_dual_scope` and `ereal_scope`
  + variants `posnume_spec` and `nonnege_spec`
  + definitions `posnume`, `nonnege`, `abse_reality_subdef`,
    `ereal_sup_reality_subdef`, `ereal_inf_reality_subdef`
  + lemmas `ereal_comparable`, `pinfty_snum_subproof`, `ninfty_snum_subproof`,
    `EFin_snum_subproof`, `fine_snum_subproof`, `oppe_snum_subproof`,
    `adde_snum_subproof`, `dadde_snum_subproof`, `mule_snum_subproof`,
    `abse_reality_subdef`, `abse_snum_subproof`, `ereal_sup_snum_subproof`,
    `ereal_inf_snum_subproof`, `num_abse_eq0`, `num_lee_maxr`, `num_lee_maxl`,
    `num_lee_minr`, `num_lee_minl`, `num_lte_maxr`, `num_lte_maxl`,
    `num_lte_minr`, `num_lte_minl`, `num_abs_le`, `num_abs_lt`,
    `posnumeP`, `nonnegeP`
  + signed instances `pinfty_snum`, `ninfty_snum`, `EFin_snum`, `fine_snum`,
    `oppe_snum`, `adde_snum`, `dadde_snum`, `mule_snum`, `abse_snum`,
    `ereal_sup_snum`, `ereal_inf_snum`

### Changed

- in `functions.v`:
  + `addrfunE` renamed to `addrfctE` and generalized to `Type`, `zmodType`
  + `opprfunE` renamed to `opprfctE` and generalized to `Type`, `zmodType`
- moved from `functions.v` to `classical_sets.v`
  + lemma `subsetW`, definition `subsetCW`
- in `mathcomp_extra.v`:
  + fix notation `ltLHS`

### Renamed

- in `topology.v`:
  + `open_bigU` -> `bigcup_open`
- in `functions.v`:
  + `mulrfunE` -> `mulrfctE`
  + `scalrfunE` -> `scalrfctE`
  + `exprfunE` -> `exprfctE`
  + `valLr` -> `valR`
  + `valLr_fun` -> `valR_fun`
  + `valLrK` -> `valRK`
  + `oinv_valLr` -> `oinv_valR`
  + `valLr_inj_subproof` -> `valR_inj_subproof`
  + `valLr_surj_subproof` -> `valR_surj_subproof`
- in `measure.v`:
  + `measurable_bigcup` -> `bigcupT_measurable`
  + `measurable_bigcap` -> `bigcapT_measurable`
  + `measurable_bigcup_rat` -> `bigcupT_measurable_rat`
- in `lebesgue_measure.v`:
  + `emeasurable_bigcup` -> `bigcupT_emeasurable`

### Removed

- files `posnum.v` and `nngnum.v` (both subsumed by `signed.v`)
- in `topology.v`:
  + `ltr_distlC`, `ler_distlC`

## [0.4.0] - 2022-03-08

### Added

- in `mathcomp_extra.v`:
  + lemma `all_sig2_cond`
  + definition `olift`
  + lemmas `obindEapp`, `omapEbind`, `omapEapp`, `oappEmap`, `omap_comp`, `oapp_comp`,
    `oapp_comp_f`, `olift_comp`, `compA`, `can_in_pcan`, `pcan_in_inj`, `can_in_comp`,
    `pcan_in_comp`, `ocan_comp`, `pred_omap`, `ocan_in_comp`, `eqbLR`, `eqbRL`
  + definition `opp_fun`, notation `\-`
  + definition `mul_fun`, notation `\*`
  + definition `max_fun`, notation `\max`
  + lemmas `gtr_opp`, `le_le_trans`
  + notations `eqLHS`, `eqRHS`, `leLHS`, `leRHS`, `ltLHS`, `lrRHS`
  + inductive `boxed`
  + lemmas `eq_big_supp`, `perm_big_supp_cond`, `perm_big_supp`
  + lemmma `mulr_ge0_gt0`
  + lemmas `lt_le`, `gt_ge`
  + coercion `pair_of_interval`
  + lemmas `ltBSide`, `leBSide`
  + multirule `lteBSide`
  + lemmas `ltBRight_leBLeft`, `leBRight_ltBLeft`
  + multirule `bnd_simp`
  + lemmas `itv_splitU1`, `itv_split1U`
  + definition `miditv`
  + lemmas `mem_miditv`, `miditv_bnd2`, `miditv_bnd1`
  + lemmas `predC_itvl`, `predC_itvr`, `predC_itv`
- in `boolp.v`:
  + lemmas `cid2`, `propeqP`, `funeqP`, `funeq2P`, `funeq3P`, `predeq2P`,
    `predeq3P`
  + hint `Prop_irrelevance`
  + lemmas `pselectT`, `eq_opE`
  + definition `classicType`, canonicals `classicType_eqType`,
    `classicType_choiceType`, notation `{classic ...}`
  + definition `eclassicType`, canonicals `eclassicType_eqType`,
    `eclassicType_choiceType`, notation `{eclassic ...}`
  + definition `canonical_of`, notations `canonical_`, `canonical`, lemma `canon`
  + lemmas `Peq`, `Pchoice`, `eqPchoice`
  + lemmas `contra_notT`, `contraPT`, `contraTP`, `contraNP`,
    `contraNP`, `contra_neqP`, `contra_eqP`
  + lemmas `forallPNP`, `existsPNP`
  + module `FunOrder`, lemma `lefP`
  + lemmas `meetfE` and `joinfE`
- in `classical_sets.v`:
  + notations `[set: ...]`, ``` *` ```, ``` `* ```
  + definitions `setMR` and `setML`, `disj_set`
  + coercion `set_type`, definition `SigSub`
  + lemmas `set0fun`, `set_mem`, `mem_setT`, `mem_setK`, `set_memK`,
    `memNset`, `setTPn`, `in_set0`, `in_setT`, `in_setC`, `in_setI`,
    `in_setD`, `in_setU`, `in_setM`, `set_valP`, `set_true`, `set_false`, `set_andb`,
    `set_orb`, `fun_true`, `fun_false`, `set_mem_set`, `mem_setE`,
    `setDUK`, `setDUK`, `setDKU`, `setUv`, `setIv`, `setvU`, `setvI`, `setUCK`,
    `setUKC`, `setICK`, `setIKC`, `setDIK`, `setDKI`, `setI1`, `set1I`,
    `subsetT`, `disj_set2E`, `disj_set2P`, `disj_setPS`, `disj_set_sym`,
    `disj_setPCl`, `disj_setPCr`, `disj_setPLR`, `disj_setPRL`, `setF_eq0`,
    `subsetCl`, `subsetCr`, `subsetC2`, `subsetCP`, `subsetCPl`, `subsetCPr`,
    `subsetUl`, `subsetUr`, `setDidl`, `subIsetl`, `subIsetr`, `subDsetl`, `subDsetr`
    `setUKD`, `setUDK`, `setUIDK`, `bigcupM1l`, `bigcupM1r`, `pred_omapE`, `pred_omap_set`
  + hints `subsetUl`, `subsetUr`, `subIsetl`, `subIsetr`, `subDsetl`, `subDsetr`
  + lemmas `image2E`
  + lemmas `Iiota`, `ordII`, `IIord`, `ordIIK`, `IIordK`
  + lemmas `set_imfset`, `imageT`
  + hints `imageP`, `imageT`
  + lemmas `homo_setP`, `image_subP`, `image_sub`, `subset_set2`
  + lemmas `eq_preimage`, `comp_preimage`, `preimage_id`, `preimage_comp`,
    `preimage_setI_eq0`, `preimage0eq`, `preimage0`, `preimage10`,
  + lemmas `some_set0`, `some_set1`, `some_setC`, `some_setR`, `some_setI`, `some_setU`,
    `some_setD`, `sub_image_some`, `sub_image_someP`, `image_some_inj`, `some_set_eq0`,
    `some_preimage`, `some_image`, `disj_set_some`
  + lemmas `some_bigcup`, `some_bigcap`, `bigcup_set_type`, `bigcup_mkcond`,
    `bigcup_mkcondr`, `bigcup_mkcondl`, `bigcap_mkcondr`, `bigcap_mkcondl`,
    `bigcupDr`, `setD_bigcupl`, `bigcup_bigcup_dep`, `bigcup_bigcup`, `bigcupID`.
    `bigcapID`
  + lemmas `bigcup2inE`, `bigcap2`, `bigcap2E`, `bigcap2inE`
  + lemmas `bigcup_sub`, `sub_bigcap`, `subset_bigcup`, `subset_bigcap`, `bigcap_set_type`, `bigcup_pred`
  + lemmas `bigsetU_bigcup2`, `bigsetI_bigcap2`
  + lemmas `in1TT`, `in2TT`, `in3TT`, `inTT_bij`
  + canonical `option_pointedType`
  + notations `[get x | E]`, `[get x : T | E]`
  + variant `squashed`, notation `$| ... |`, tactic notation `squash`
  + definition `unsquash`, lemma `unsquashK`
  + module `Empty` that declares the type `emptyType` with the expected `[emptyType of ...]` notations
  + canonicals `False_emptyType` and `void_emptyType`
  + definitions `no` and `any`
  + lemmas `empty_eq0`
  + definition `quasi_canonical_of`, notations `quasi_canonical_`, `quasi_canonical`, lemma `qcanon`
  + lemmas `choicePpointed`, `eqPpointed`, `Ppointed`
  + lemmas `trivIset_setIl`, `trivIset_setIr`, `sub_trivIset`, `trivIset_bigcup2`
  + definition `smallest`
  + lemmas `sub_smallest`, `smallest_sub`, `smallest_id`
  + lemma and hint `sub_gen_smallest`
  + lemmas `sub_smallest2r`, `sub_smallest2l`
  + lemmas `preimage_itv`, `preimage_itv_o_infty`, `preimage_itv_c_infty`, `preimage_itv_infty_o`,
    `preimage_itv_infty_c`, `notin_setI_preimage`
  + definitions `xsection`, `ysection`
  + lemmas `xsection0`, `ysection0`, `in_xsectionM`, `in_ysectionM`, `notin_xsectionM`, `notin_ysectionM`,
    `xsection_bigcup`, `ysection_bigcup`, `trivIset_xsection`, `trivIset_ysection`, `le_xsection`,
    `le_ysection`, `xsectionD`, `ysectionD`
- in `topology.v`:
  + lemma `filter_pair_set`
  + definition `prod_topo_apply`
  + lemmas `prod_topo_applyE`, `prod_topo_apply_continuous`, `hausdorff_product`
  + lemmas `closedC`, `openC`
  + lemmas `continuous_subspace_in`
  + lemmas`closed_subspaceP`, `closed_subspaceW`, `closure_subspaceW`
  + lemmas `nbhs_subspace_subset`, `continuous_subspaceW`, `nbhs_subspaceT`,
    `continuous_subspaceT_for`, `continuous_subspaceT`, `continuous_open_subspace`
  + globals `subspace_filter`, `subspace_proper_filter`
  + notation `{within ..., continuous ...}`
  + definitions `compact_near`, `precompact`, `locally_compact`
  + lemmas `precompactE`, `precompact_subset`, `compact_precompact`,
    `precompact_closed`
  + definitions `singletons`, `equicontinuous`, `pointwise_precompact`
  + lemmas `equicontinuous_subset`, `equicontinuous_cts`
  + lemmas `pointwise_precomact_subset`, `pointwise_precompact_precompact`
    `uniform_pointwise_compact`, `compact_pointwise_precompact`
  + lemmas `compact_set1`, `uniform_set1`, `ptws_cvg_family_singleton`,
    `ptws_cvg_compact_family`
  + lemmas `connected1`, `connectedU`
  + lemmas `connected_component_sub`, `connected_component_id`,
    `connected_component_out`, `connected_component_max`, `connected_component_refl`,
    `connected_component_cover`, `connected_component_cover`, `connected_component_trans`,
    `same_connected_component`
  + lemma `continuous_is_cvg`
  + lemmas `uniform_limit_continuous`, `uniform_limit_continuous_subspace`
- in `normedtype.v`
  + generalize `IVT` with subspace topology
  + lemmas `abse_continuous`, `cvg_abse`, `is_cvg_abse`, `EFin_lim`, `near_infty_natSinv_expn_lt`
- in `reals.v`:
  + lemmas `sup_gt`, `inf_lt`, `ltr_add_invr`
- in `ereal.v`:
  + lemmas `esum_ninftyP`, `esum_pinftyP`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinftyP`, `desum_ninftyP`
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`
  + lemmas `mule_def_fin`, `mule_def_neq0_infty`, `mule_def_infty_neq0`, `neq0_mule_def`
  + notation `\-` in `ereal_scope` and `ereal_dual_scope`
  + lemma `fin_numB`
  + lemmas `mule_eq_pinfty`, `mule_eq_ninfty`
  + lemmas `fine_eq0`, `abse_eq0`
  + lemmas `EFin_inj`, `EFin_bigcup`, `EFin_setC`, `adde_gt0`, `mule_ge0_gt0`,
    `lte_mul_pinfty`, `lt0R`, `adde_defEninfty`, `lte_pinfty_eq`, `ge0_fin_numE`, `eq_pinftyP`,
  + canonical `mule_monoid`
  + lemmas `preimage_abse_pinfty`, `preimage_abse_ninfty`
  + notation `\-`
  + lemmas `fin_numEn`, `fin_numPn`, `oppe_eq0`, `ltpinfty_adde_def`,
    `gte_opp`, `gte_dopp`, `gt0_mulpinfty`, `lt0_mulpinfty`, `gt0_mulninfty`, `lt0_mulninfty`,
    `eq_infty`, `eq_ninfty`, `hasNub_ereal_sup`, `ereal_sup_EFin`, `ereal_inf_EFin`,
    `restrict_abse`
  + canonical `ereal_pointed`
  + lemma `seq_psume_eq0`
  + lemmas `lte_subl_addl`, `lte_subr_addl`, `lte_subel_addr`,
    `lte_suber_addr`, `lte_suber_addl`, `lee_subl_addl`,
    `lee_subr_addl`, `lee_subel_addr`, `lee_subel_addl`,
    `lee_suber_addr`, `lee_suber_addl`
  + lemmas `lte_dsubl_addl`, `lte_dsubr_addl`, `lte_dsubel_addr`,
    `lte_dsuber_addr`, `lte_dsuber_addl`, `lee_dsubl_addl`,
    `lee_dsubr_addl`, `lee_dsubel_addr`, `lee_dsubel_addl`,
    `lee_dsuber_addr`, `lee_dsuber_addl`
  + lemmas `realDe`, `realDed`, `realMe`, `nadde_eq0`, `padde_eq0`,
    `adde_ss_eq0`, `ndadde_eq0`, `pdadde_eq0`, `dadde_ss_eq0`,
    `mulrpinfty_real`, `mulpinftyr_real`, `mulrninfty_real`,
    `mulninftyr_real`, `mulrinfty_real`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`
  + definition `eseries` with notation `[eseries E]_n`
    + lemmas `eseriesEnat`, `eseriesEord`, `eseriesSr`, `eseriesS`,
      `eseriesSB`, `eseries_addn`, `sub_eseries_geq`, `sub_eseries`,
      `sub_double_eseries`, `eseriesD`
  + definition `etelescope`
  + lemmas `ereal_cvgB`, `nondecreasing_seqD`, `lef_at`
  + lemmas `lim_mkord`, `ereal_pseries_mkcond`, `ereal_pseries_sum`
  + definition `sdrop`
  + lemmas `has_lbound_sdrop`, `has_ubound_sdrop`
  + definitions `sups`, `infs`
  + lemmas `supsN`, `infsN`, `nonincreasing_sups`, `nondecreasing_infs`, `is_cvg_sups`, `is_cvg_infs`,
    `infs_le_sups`, `cvg_sups_inf`, `cvg_infs_sup`, `sups_preimage`, `infs_preimage`, `bounded_fun_has_lbound_sups`,
    `bounded_fun_has_ubound_infs`
  + definitions `lim_sup`, `lim_inf`
  + lemmas `lim_infN`, `lim_supE`, `lim_infE`, `lim_inf_le_lim_sup`, `cvg_lim_inf_sup`,
    `cvg_lim_infE`, `cvg_lim_supE`, `cvg_sups`, `cvg_infs`, `le_lim_supD`, `le_lim_infD`,
    `lim_supD`, `lim_infD`
  + definitions `esups`, `einfs`
  + lemmas `esupsN`, `einfsN`, `nonincreasing_esups`, `nondecreasing_einfs`, `einfs_le_esups`,
    `cvg_esups_inf`, `is_cvg_esups`, `cvg_einfs_sup`, `is_cvg_einfs`, `esups_preimage`, `einfs_preimage`
  + definitions `elim_sup`, `elim_inf`
  + lemmas `elim_infN`, `elim_supN`, `elim_inf_sup`, `elim_inf_sup`, `cvg_ninfty_elim_inf_sup`,
    `cvg_ninfty_einfs`, `cvg_ninfty_esups`, `cvg_pinfty_einfs`, `cvg_pinfty_esups`, `cvg_esups`,
    `cvg_einfs`, `cvg_elim_inf_sup`, `is_cvg_elim_infE`, `is_cvg_elim_supE`
  + lemmas `elim_inf_shift`, `elim_sup_le_cvg`
- in `derive.v`
  + lemma `MVT_segment`
  + lemma `derive1_cst`
- in `realfun.v`:
  + lemma `continuous_subspace_itv`
- in `esum.v` (was `csum.v`):
  + lemmas `sum_fset_set`, `esum_ge`, `esum0`, `le_esum`, `eq_esum`, `esumD`,
    `esum_mkcond`, `esum_mkcondr`, `esum_mkcondl`, `esumID`, `esum_sum`,
    `esum_esum`, `lee_sum_fset_nat`, `lee_sum_fset_lim`, `ereal_pseries_esum`, `reindex_esum`,
    `esum_pred_image`, `esum_set_image`, `esum_bigcupT`
- in `cardinality.v`:
  + notations `#>=`, `#=`, `#!=`
  + scope `card_scope`, delimiter `card`
  + notation `infinite_set`
  + lemmas `injPex`, `surjPex`, `bijPex`, `surjfunPex`, `injfunPex`
  + lemmas `inj_card_le`, `pcard_leP`, `pcard_leTP`, `pcard_injP`, `ppcard_leP`
  + lemmas `pcard_eq`, `pcard_eqP`, `card_bijP`, `card_eqVP`, `card_set_bijP`
  + lemmas `ppcard_eqP`, `card_eqxx`, `inj_card_eq`, `card_some`, `card_image`,
    `card_imsub`
  + hint `card_eq00`
  + lemmas `empty_eq0`, `card_le_emptyl`, `card_le_emptyr`
  + multi-rule `emptyE_subdef`
  + lemmas `card_eq_le`, `card_eqPle`, `card_leT`, `card_image_le`
  + lemmas `card_le_eql`, `card_le_eqr`, `card_eql`, `card_eqr`,
    `card_ge_image`, `card_le_image`, `card_le_image2`, `card_eq_image`, `card_eq_imager`,
    `card_eq_image2`
  + lemmas `card_ge_some`, `card_le_some`, `card_le_some2`, `card_eq_somel`, `card_eq_somer`,
    `card_eq_some2`
  + lemmas `card_eq_emptyr`, `card_eq_emptyl`, `emptyE`
  + lemma and hint `card_setT`
  + lemma and hint `card_setT_sym`
  + lemmas `surj_card_ge`, `pcard_surjP`, `pcard_geP`, `ocard_geP`, `pfcard_geP`
  + lemmas `ocard_eqP`, `oocard_eqP`, `sub_setP`, `card_subP`
  + lemmas `eq_countable`, `countable_set_countMixin`, `countableP`, `sub_countable`
  + lemmas `card_II`, `finite_fsetP`, `finite_subfsetP`, `finite_seqP`, `finite_fset`, `finite_finpred`,
    `finite_finset`, `infiniteP`, `finite_setPn`
  + lemmas `card_le_finite`, `finite_set_leP`, `card_ge_preimage`, `eq_finite_set`,
    `finite_image`
  + lemma and hint `finite_set1`
  + lemmas `finite_setU`, `finite_set2`, `finite_set3`, `finite_set4`, `finite_set5`,
    `finite_set6`, `finite_set7`, `finite_setI`, `finite_setIl`, `finite_setIr`,
    `finite_setM`, `finite_image2`, `finite_image11`
  + definition `fset_set`
  + lemmas `fset_setK`, `in_fset_set`, `fset_set0`, `fset_set1`, `fset_setU`,
    `fset_setI`, `fset_setU1`, `fset_setD`, `fset_setD1`, `fset_setM`
  + definitions `fst_fset`, `snd_fset`, notations ``` .`1 ```, ``` .`2 ```
  + lemmas `finite_set_fst`, `finite_set_snd`, `bigcup_finite`, `finite_setMR`, `finite_setML`,
    `fset_set_II`, `set_fsetK`, `fset_set_inj`, `bigsetU_fset_set`, `bigcup_fset_set`,
    `bigsetU_fset_set_cond`, `bigcup_fset_set_cond`, `bigsetI_fset_set`, `bigcap_fset_set`,
    `super_bij`, `card_eq_fsetP`, `card_IID`, `finite_set_bij`
  + lemmas `countable1`, `countable_fset`
  + lemma and hint `countable_finpred`
  + lemmas `eq_card_nat`
  + canonical `rat_pointedType`
  + lemmas `infinite_rat`, `card_rat`, `choicePcountable`, `eqPcountable`, `Pcountable`,
    `bigcup_countable`, `countableMR`, `countableM`, `countableML`, `infiniteMRl`, `cardMR_eq_nat`
  + mixin `FiniteImage`, structure `FImFun`, notations `{fumfun ... >-> ...}`,
    `[fimfun of ...]`, hint `fimfunP`
  + lemma and hint `fimfun_inP`
  + definitions `fimfun`, `fimfun_key`, canonical `fimfun_keyed`
  + definitions `fimfun_Sub_subproof`, `fimfun_Sub`
  + lemmas `fimfun_rect`, `fimfun_valP`, `fimfuneqP`
  + definitions and canonicals `fimfuneqMixin`, `fimfunchoiceMixin`
  + lemma `finite_image_cst`, `cst_fimfun_subproof`, `fimfun_cst`
  + definition `cst_fimfun`
  + lemma `comp_fimfun_subproof`
  + lemmas `fimfun_zmod_closed`, `fimfunD`, `fimfunN`, `fimfunB`, `fimfun0`, `fimfun_sum`
  + canonicals `fimfun_add`, `fimfun_zmod`, `fimfun_zmodType`
  + definition `fimfun_zmodMixin`
- in `measure.v`:
  + definitions `setC_closed`, `setI_closed`, `setU_closed`, `setD_closed`, `setDI_closed`,
    `fin_bigcap_closed`, `finN0_bigcap_closed`, `fin_bigcup_closed`, `semi_setD_closed`,
    `ndseq_closed`, `trivIset_closed`, `fin_trivIset_closed`, `set_ring`, `sigma_algebra`,
    `dynkin`, `monotone_classes`
  + notations `<<m D, G >>`, `<<m G >>`, `<<s D, G>>`, `<<s G>>`, `<<d G>>`, `<<r G>>`, `<<fu G>>`
  + lemmas `fin_bigcup_closedP`, `finN0_bigcap_closedP`,
    `sedDI_closedP`, `sigma_algebra_bigcap`, `sigma_algebraP`
  + lemma and hint `smallest_sigma_algebra`
  + lemmas `sub_sigma_algebra2`, `sigma_algebra_id`, `sub_sigma_algebra`, `sigma_algebra0`,
    `sigma_algebraD`, `sigma_algebra_bigcup`
  + lemma and hint `smallest_setring`, lemma and hint `setring0`
  + lemmas `sub_setring2`, `setring_id`, `sub_setring`, `setringDI`, `setringU`,
    `setring_fin_bigcup`, `monotone_class_g_salgebra`
  + lemmas `smallest_monotone_classE`, `monotone_class_subset`, `dynkinT`, `dynkinC`, `dynkinU`,
    `dynkin_monotone`, `dynkin_g_dynkin`, `sigma_algebra_dynkin`, `dynkin_setI_bigsetI`,
    `dynkin_setI_sigma_algebra`, `setI_closed_gdynkin_salgebra`
  + factories `isRingOfSets`, `isAlgebraOfSets`
  + lemmas `fin_bigcup_measurable`, `fin_bigcap_measurable`, `sigma_algebra_measurable`,
    `sigma_algebraC`
  + definition `measure_restr`, lemma `measure_restrE`
  + definition `g_measurableType`
  + lemmas `measurable_g_measurableTypeE`
  + lemmas `measurable_fun_id`, `measurable_fun_comp`, `eq_measurable_fun`, `measurable_fun_cst`,
    `measurable_funU`, `measurable_funS`,  `measurable_fun_ext`, `measurable_restrict`
  + definitions `preimage_class` and `image_class`
  + lemmas `preimage_class_measurable_fun`, `sigma_algebra_preimage_class`, `sigma_algebra_image_class`,
    `sigma_algebra_preimage_classE`, `measurability`
  + definition `sub_additive`
  + lemma `semi_additiveW`
  + lemmas `content_fin_bigcup`, `measure_fin_bigcup`, `measure_bigsetU_ord_cond`, `measure_bigsetU_ord`,
  + coercion `measure_to_nadditive_measure`
  + lemmas `measure_semi_bigcup`, `measure_bigcup`
  + hint `measure_ge0`
  + lemma `big_trivIset`
  + defintion `covered_by`
  + module `SetRing`
    * lemmas `ring_measurableE`, `ring_fsets`
    * definition `decomp`
    * lemmas `decomp_triv`, `decomp_triv`, `decomp_neq0`, `decomp_neq0`, `decomp_measurable`, `cover_decomp`,
      `decomp_sub`, `decomp_set0`, `decomp_set0`
    * definition `measure`
    * lemma `Rmu_fin_bigcup`, `RmuE`, `Rmu0`, `Rmu_ge0`, `Rmu_additive`, `Rmu_additive_measure`
    * canonical `measure_additive_measure`
  + lemmas `covered_byP`, `covered_by_finite`, `covered_by_countable`,
    `measure_le0`, `content_sub_additive`, `content_sub_fsum`,
    `content_ring_sup_sigma_additive`, `content_ring_sigma_additive`, `ring_sigma_sub_additive`,
    `ring_sigma_additive`, `measure_sigma_sub_additive`, `measureIl`, `measureIr`,
    `subset_measure0`, `measureUfinr`, `measureUfinl`, `eq_measureU`, `null_set_setU`
  + lemmas `g_salgebra_measure_unique_trace`, `g_salgebra_measure_unique_cover`, `g_salgebra_measure_unique`,
    `measure_unique`, `measurable_mu_extE`, `Rmu_ext`, `measurable_Rmu_extE`,
    `sub_caratheodory`
  + definition `Hahn_ext`, canonical `Hahn_ext_measure`, lemma `Hahn_ext_sigma_finite`, `Hahn_ext_unique`,
    `caratheodory_measurable_mu_ext`
  + definitions `preimage_classes`, `prod_measurable`, `prod_measurableType`
  + lemmas `preimage_classes_comp`, `measurableM`, `measurable_prod_measurableType`, `measurable_prod_g_measurableTypeR`,
    `measurable_prod_g_measurableType`, `prod_measurable_funP`, `measurable_fun_prod1`, `measurable_fun_prod2`
- in `functions.v`:
  + definitions `set_fun`, `set_inj`
  + mixin `isFun`, structure `Fun`, notations `{fun ... >-> ...}`, `[fun of ...]`
    * field `funS` declared as a hint
  + mixin `OInv`, structure `OInversible`, notations `{oinv ... >-> ...}`, `[oinv of ...]`, `'oinv_ ...`
  + structure `OInvFun`, notations `{oinvfun ... >-> ...}`, `[oinvfun of ...]`
  + mixin `OInv_Inv`, factory `Inv`, structure `Inversible`, notations `{inv ... >-> ...}`, `[inv of ...]`, notation `^-1`
  + structure `InvFun`, notations `{invfun ... >-> ...}`, `[invfun of ...]`
  + mixin `OInv_CanV` with field `oinvK` declared as a hint, factory `OCanV`
  + structure `Surject`, notations `{surj ... >-> ...}`, `[surj of ...]`
  + structure `SurjFun`, notations `{surjfun ... >-> ...}`, `[surjfun of ...]`
  + structure `SplitSurj`, notations `{splitsurj ... >-> ...}`, `[splitsurj of ...]`
  + structure `SplitSurjFun`, notations `{splitsurjfun ... >-> ...}`, `[splitsurjfun of ...]`
  + mixin `OInv_Can` with field `funoK` declared as a hint, structure `Inject`, notations `{inj ... >-> ...}`, `[inj of ...]`
  + structure `InjFun`, notations `{injfun ... >-> ...}`, `[injfun of ...]`
  + structure `SplitInj`, notations `{splitinj ... >-> ...}`, `[splitinj of ...]`
  + structure `SplitInjFun`, notations `{splitinjfun ... >-> ...}`, `[splitinjfun of ...]`
  + structure `Bij`, notations `{bij ... >-> ...}`, `[bij of ...]`
  + structure `SplitBij`, notations `{splitbij ... >-> ...}`, `[splitbij of ...]`
  + module `ShortFunSyntax` for shorter notations
  + notation `'funS_ ...`
  + definition and hint `fun_image_sub`
  + definition and hint `mem_fun`
  + notation `'mem_fun_ ...`
  + lemma `some_inv`
  + notation `'oinvS_ ...`
  + variant `oinv_spec`, lemma and hint `oinvP`
  + notation `'oinvP_ ...`
  + lemma and hint `oinvT`, notation `'oinvT_ ...`
  + lemma and hint `invK`, notation `'invK_ ...`
  + lemma and hint `invS`, notation `'invS_ ...`
  + notation `'funoK_ ...`
  + definition `inj` and notation `'inj_ ...`
  + definition and hint `inj_hint`
  + lemma and hint `funK`, notation `'funK_ ...`
  + lemma `funP`
  + factories `Inv_Can`, `Inv_CanV`
  + lemmas `oinvV`, `surjoinv_inj_subproof`, `injoinv_surj_subproof`, `invV`, `oinv_some`,
    `some_canV_subproof`, `some_fun_subproof`, `inv_oapp`, `oinv_oapp`, `inv_oappV`,
    `oapp_can_subproof`, `oapp_surj_subproof`, `oapp_fun_subproof`, `inv_obind`, `oinv_obind`,
    `inv_obindV`, `oinv_comp`, `some_comp_inv`, `inv_comp`, `comp_can_subproof`, `comp_surj_subproof`,
  + notation `'totalfun_ ...`
  + lemmas `oinv_olift`, `inv_omap`, `oinv_omap`, `omapV`
  + factories `canV`, `OInv_Can2`, `OCan2`, `Can`, `Inv_Can2`, `Can2`, `SplitInjFun_CanV`, `BijTT`
  + lemmas `surjective_oinvK`, `surjective_oinvS`, coercion `surjective_ocanV`
  + definition and coercion `surjection_of_surj`, lemma `Psurj`, coercion `surjection_of_surj`
  + lemma `oinv_surj`, lemma and hint `surj`, notation `'surj_`
  + definition `funin`, lemma `set_fun_image`, notation `[fun ... in ...]`
  + definition `split_`, lemmas `splitV`, `splitis_inj_subproof`, `splitid`, `splitsurj_subproof`,
    notation `'split_`, `split`
  + factories `Inj`, `SurjFun_Inj`, `SplitSurjFun_Inj`
  + lemmas `Pinj`, `Pfun`, `injPfun`, `funPinj`, `funPsurj`, `surjPfun`, `Psplitinj`, `funPsplitinj`,
    `PsplitinjT`, `funPsplitsurj`, `PsplitsurjT`
  + definition `unbind`
  + lemmas `unbind_fun_subproof`, `oinv_unbind`, `inv_unbind_subproof`, `inv_unbind`, `unbind_inj_subproof`,
    `unbind_surj_subproof`, `odflt_unbind`, `oinv_val`, `val_bij_subproof`, `inv_insubd`
  + definition `to_setT`, lemma `inv_to_setT`
  + definition `subfun`, lemma `subfun_inj`
  + lemma `subsetW`, definition `subsetCW`
  + lemmas `subfun_imageT`, `subfun_inv_subproof`
  + definition `seteqfun`, lemma `seteqfun_can2_subproof`
  + definitions `incl`, `eqincl`, lemma `eqincl_surj`, notation `inclT`
  + definitions `mkfun`, `mkfun_fun`
  + definition `set_val`, lemmas `oinv_set_val`, `set_valE`
  + definition `ssquash`
  + lemma `set0fun_inj`
  + definitions `finset_val`, `val_finset`
  + lemmas `finset_valK`, `val_finsetK`
  + definition `glue`, `glue1`, `glue2`, lemmas `glue_fun_subproof`, `oinv_glue`, `some_inv_glue_subproof`,
    `inv_glue`, `glueo_can_subproof`, `glue_canv_subproof`
  + lemmas `inv_addr`, `addr_can2_subproof`
  + lemmas `empty_can_subproof`, `empty_fun_subproof`, `empty_canv_subproof`
  + lemmas `subl_surj`, `subr_surj`, `surj_epi`, `epiP`, `image_eq`, `oinv_image_sub`,
    `oinv_Iimage_sub`, `oinv_sub_image`, `inv_image_sub`, `inv_Iimage_sub`, `inv_sub_image`,
    `reindex_bigcup`, `reindex_bigcap`, `bigcap_bigcup`, `trivIset_inj`, `set_bij_homo`
  + definition and hint `fun_set_bij`
  + coercion `set_bij_bijfun`
  + definition and coercion `bij_of_set_bijection`
  + lemma and hint `bij`, notation `'bij_`
  + definition `bijection_of_bijective`, lemmas `PbijTT`, `setTT_bijective`,
    lemma and hint `bijTT`, notation `'bijTT_`
  + lemmas `patchT`, `patchN`, `patchC`, `patch_inj_subproof`,
    `preimage_restrict`, `comp_patch`,
    `patch_setI`, `patch_set0`, `patch_setT`, `restrict_comp`
  + definitions `sigL`, `sigLfun`, `valL_`, `valLfun_`
  + lemmas `sigL_isfun`, `valL_isfun`, `sigLE`, `eq_sigLP`, `eq_sigLfunP`, `sigLK`, `valLK`,
    `valLfunK`, `sigL_valL`, `sigL_valLfun\`, `sigL_restrict`, `image_sigL`, `eq_restrictP`
  + notations `'valL_ ...`, `'valLfun_ ...`, `valL`
  + definitions `sigR`, `valLr`, `valLr_fun`
  + lemmas `sigRK`, `sigR_funK`, `valLrP`, `valLrK`
  + lemmas `oinv_sigL`, `sigL_inj_subproof`, `sigL_surj_subproof`, `oinv_sigR`, `sigR_inj_subproof`,
    `sigR_surj_subproof`, `sigR_some_inv`, `inv_sigR`, `sigL_some_inv`, `inv_sigL`,
    `oinv_valL`, `oapp_comp_x`, `valL_inj_subproof`, `valL_surj_subproof`, `valL_some_inv`,
    `inv_valL`, `sigL_injP`, `sigL_surjP`, `sigL_funP`, `sigL_bijP`, `valL_injP`, `valL_surjP`,
    `valLfunP`, `valL_bijP`
  + lemmas `oinv_valLr`, `valLr_inj_subproof`, `valLr_surj_subproof`
  + definitions `sigLR`, `valLR`, `valLRfun`, lemmas `valLRE`, `valLRfunE`, `sigL2K`,
    `valLRK`, `valLRfun_inj`, `sigLR_injP`, `valLR_injP`, `sigLR_surjP`, `valLR_surjP`,
    `sigLR_bijP`, `sigLRfun_bijP`, `valLR_bijP`, `subsetP`
  + new lemmas `eq_set_bijLR`, `eq_set_bij`, `bij_omap`, `bij_olift`, `bij_sub_sym`,
   `splitbij_sub_sym`, `set_bij00`, `bij_subl`, `bij_sub`, `splitbij_sub`, `can2_bij`,
   `bij_sub_setUrl`, `bij_sub_setUrr`, `bij_sub_setUrr`, `bij_sub_setUlr`
  + definition `pinv_`, lemmas `injpinv_surj`, `injpinv_image`,
    `injpinv_bij`, `surjpK`, `surjpinv_image_sub`, `surjpinv_inj`, `surjpinv_bij`,
    `bijpinv_bij`, `pPbij_`, `pPinj_`, `injpPfun_`, `funpPinj_`
- in `fsbigop.v`:
  + notations `\big[op/idx]_(i \in A) f i`, `\sum_(i \in A) f i`
  + lemma `finite_index_key`
  + definition `finite_support`
  + lemmas `in_finite_support`, `no_finite_support`, `eq_finite_support`
  + variant `finite_support_spec`
  + lemmas  `finite_supportP`, `eq_fsbigl`, `eq_fsbigr`,
    `fsbigTE`, `fsbig_mkcond`, `fsbig_mkcondr`, `fsbig_mkcondl`, `bigfs`,
    `fsbigE`, `fsbig_seq`, `fsbig1`, `fsbig_dflt`, `fsbig_widen`, `fsbig_supp`,
    `fsbig_fwiden`, `fsbig_set0`, `fsbig_set1`, `full_fsbigID`, `fsbigID`, `fsbigU`,
    `fsbigU0`, `fsbigD1`, `full_fsbig_distrr`, `fsbig_distrr`, `mulr_fsumr`, `mulr_fsuml`,
    `fsbig_ord`, `fsbig_finite`, `reindex_fsbig`, `fsbig_image`, `reindex_inside`,
    `reindex_fsbigT`, notation `reindex_inside_setT`
  + lemmas `ge0_mule_fsumr`, `ge0_mule_fsuml`, `fsbigN1`, `fsume_ge0`, `fsume_le0`,
    `fsume_gt0`, `fsume_lt0`, `pfsume_eq0`, `fsbig_setU`, `pair_fsum`, `exchange_fsum`,
    `fsbig_split`
- in `set_interval.v`:
  + definition `neitv`
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itvco`, `set_itvcc`,
    `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`, `set_itv_infty_infty`, `set_itv_o_infty`,
    `set_itv_c_infty`, `set_itv_infty_o`, `set_itv_infty_c`, `set_itv_pinfty_bnd`,
    `set_itv_bnd_ninfty`
  + multirules `set_itv_infty_set0`, `set_itvE`
  + lemmas `setUitv1`, `setU1itv`
  + lemmas `neitvE`, `neitvP`, `setitv0`
  + lemmas `set_itvI`
  + lemmas and hints `has_lbound_itv`, `has_ubound_itv`, `hasNlbound_itv`, `hasNubound_itv`,
    `has_sup_half`, `has_inf_half`
  + lemmas `opp_itv_bnd_infty`, `opp_itvoo`,
    `sup_itv`, `inf_itv`, `sup_itvcc`, `inf_itvcc`
    `setCitvl`, `setCitvr`, `setCitv`
  + lemmas `set_itv_splitD`, `set_itvK`, `RhullT`, `RhullK`,
    `itv_c_inftyEbigcap`, `itv_bnd_inftyEbigcup`, `itv_o_inftyEbigcup`, `set_itv_setT`,
    `set_itv_ge`
  + definitions `conv`, `factor`
  + lemmas `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`, `conv1`, `conv_sym`,
    `conv_flat`, `factorl`, `factorr`, `factor_flat`, `mem_1B_itvcc`, `factorK`,
    `convK`, `conv_inj`, `conv_bij`, `factor_bij`, `leW_conv`, `leW_factor`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`
  + definition `ndconv`
  + lemmas `ndconvE`, `conv_itv_bij`, `conv_itv_bij`, `factor_itv_bij`, `mem_conv_itv`,
    `mem_factor_itv`, `mem_conv_itvcc`, `range_conv`, `range_factor`, `Rhull_smallest`,
    `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`
  + coercion `ereal_of_itv_bound`
  + lemmas `le_bnd_ereal`, `lt_ereal_bnd`, `neitv_bnd1`, `neitv_bnd2`, `Interval_ereal_mem`,
    `ereal_mem_Interval`, `trivIset_set_itv_nth`
  + definition `disjoint_itv`
  + lemmas `disjoint_itvxx`, `lt_disjoint`, `disjoint_neitv`, `disj_itv_Rhull`
- new file `numfun.v`
  + lemmas `restrict_set0`, `restrict_ge0`, `erestrict_set0`, `erestrict_ge0`, `ler_restrict`,
    `lee_restrict`
  + definition `funenng` and notation `^\+`, definition `funennp` and notation `^\-`
  + lemmas and hints `funenng_ge0`, `funennp_ge0`
  + lemmas `funenngN`, `funennpN`, `funenng_restrict`,
    `funennp_restrict`, `ge0_funenngE`, `ge0_funennpE`, `le0_funenngE`, `le0_funennpE`,
    `gt0_funenngM`, `gt0_funennpM`, `lt0_funenngM`, `lt0_funennpM`, `fune_abse`,
    `funenngnnp`, `add_def_funennpg`, `funeD_Dnng`, `funeD_nngD`
  + definition `indic` and notation `\1_`
  + lemmas `indicE`, `indicT`, `indic0`, `indic_restrict`, `restrict_indic`, `preimage_indic`,
    `image_indic`, `image_indic_sub`
- in `trigo.v`:
  + lemmas `acos1`, `acos0`, `acosN1`, `acosN`, `cosKN`, `atan0`, `atan1`
- new file `lebesgue_measure.v`
- new file `lebesgue_integral.v`

### Changed

- in `boolp.v`:
  + `equality_mixin_of_Type`, `choice_of_Type` -> see `classicalType`
- in `topology.v`:
  + generalize `connected_continuous_connected`, `continuous_compact`
  + arguments of `subspace`
  + definition `connected_component`
- in `sequences.v`:
  + `\sum` notations for extended real numbers now in `ereal_scope`
  + lemma `ereal_cvg_sub0` is now an equivalence
- in `derive.v`:
  + generalize `EVT_max`, `EVT_min`, `Rolle`, `MVT`, `ler0_derive1_nincr`,
    `le0r_derive1_ndecr` with subspace topology
  + implicits of `cvg_at_rightE`, `cvg_at_leftE`
- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`
- in `esum.v` (was `csum.v`):
  + lemma `esum_ge0` has now a weaker hypothesis
- notation ``` `I_ ``` moved from `cardinality.v` to `classical_sets.v`
- moved from `classical_types.v` to `boolp.v`:
  + definitions `gen_eq` and `gen_eqMixin`, lemma `gen_eqP`
  + canonicals `arrow_eqType`, `arrow_choiceType`
  + definitions `dep_arrow_eqType`, `dep_arrow_choiceClass`, `dep_arrow_choiceType`
  + canonicals `Prop_eqType`, `Prop_choiceType`
- in `classical_sets.v`:
  + arguments of `preimage`
  + `[set of f]` becomes `range f` (the old notation is still available
     but is displayed as the new one, and will be removed in future versions)
- in `cardinality.v`:
  + definition `card_eq` now uses `{bij ... >-> ...}`
  + definition `card_le` now uses `{injfun ... >-> ...}`
  + definition `set_finite` changed to `finite_set`
  + definition `card_leP` now uses `reflect`
  + definition `card_le0P` now uses `reflect`
  + definition `card_eqP` now uses `reflect`
  + statement of theorem `Cantor_Bernstein`
  + lemma `subset_card_le` does not require finiteness of rhs anymore
  + lemma `surjective_card_le` does not require finiteness of rhs anymore and renamed to `surj_card_ge`
  + lemma `card_le_diff` does not require finiteness of rhs anymore and renamed to `card_le_setD`
  + lemma `card_eq_sym` now an equality
  + lemma `card_eq0` now an equality
  + lemmas `card_le_II` and `card_eq_II` now equalities
  + lemma `countable_injective` renamed to `countable_injP` and use `reflect`
  + lemmas `II0`, `II1`, `IIn_eq0` moved to `classical_sets.v`
  + lemma `II_recr` renamed to `IIS` and moved to `classical_sets.v`
  + definition `surjective` moved to `functions.v` and renamed `set_surj`
  + definition `set_bijective` moved to `functions.v` and changed to `set_bij`
  + lemma `surjective_id` moved to `functions.v` and renamed `surj_id`
  + lemma `surjective_set0` moved to `functions.v` and renamed `surj_set0`
  + lemma `surjectiveE` moved to `functions.v` and renamed `surjE`
  + lemma `surj_image_eq` moved to `functions.v`
  + lemma `can_surjective` moved to `functions.v` and changed to `can_surj`
  + lemma `surjective_comp` moved to `functions.v` and renamed `surj_comp`
  + lemma `set_bijective1` moved to `functions.v` and renamed `eq_set_bijRL`
  + lemma `set_bijective_image` moved to `functions.v` and renamed `inj_bij`
  + lemma `set_bijective_subset` moved to `functions.v` and changed to `bij_subr`
  + lemma `set_bijective_comp` moved to `functions.v` and renamed `set_bij_comp`
  + definition `inverse` changed to `pinv_`, see `functions.v`
  + lemma `inj_of_bij` moved to `functions.v` and renamed to `set_bij_inj`
  + lemma `sur_of_bij` moved to `functions.v` and renamed to `set_bij_surj`
  + lemma `sub_of_bij` moved to `functions.v` and renamed to `set_bij_sub`
  + lemma `set_bijective_D1` moved to `functions.v` and renamed to `bij_II_D1`
  + lemma `injective_left_inverse` moved to `functions.v` and changed to `pinvKV`
  + lemma `injective_right_inverse` moved to `functions.v` and changed to `pinvK`
  + lemmas `image_nat_maximum`, `fset_nat_maximum` moved to `mathcomp_extra.v`
  + lemmas `enum0`, `enum_recr` moved to `mathcomp_extra.v` and renamed to `enum_ord0`, `enum_ordS`
  + lemma `in_inj_comp` moved to `mathcomp_extra.v`
- from `cardinality.v` to `classical_sets.v`:
  + `eq_set0_nil` -> `set_seq_eq0`
  + `eq_set0_fset0` -> `set_fset_eq0`
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`  moved to `classical_sets.v`
  + mixin `isSemiRingOfSets` and `isRingOfSets` changed
  + types `semiRingOfSetsType`, `ringOfSetsType`, `algebraOfSetsType`, `measurableType` now pointed types
  + definition `measurable_fun` changed
  + definition `sigma_sub_additive` changed and renamed to `sigma_subadditive`
  + record `AdditiveMeasure.axioms`
  + lemmas `measure_ge0`
  + record `Measure.axioms`
  + definitions `seqDU`, `seqD`, lemma and hint `trivIset_seqDU`, lemmas `bigsetU_seqDU`, `seqDU_bigcup_eq`,
    `seqDUE`, `trivIset_seqD`, `bigsetU_seqD`, `setU_seqD`, `eq_bigsetU_seqD`, `eq_bigcup_seqD`, `eq_bigcup_seqD_bigsetU`
    moved to `sequences.v`
  + definition `negligibleP` weakened to additive measures
  + lemma `measure_negligible`
  + definition `caratheodory_measurable` and `caratheodory_type` weakened from outer measures to functions
  + lemma `caratheodory_measure_ge0` does take a condition anymore
  + definitions `measurable_cover` and `mu_ext`, canonical `outer_measure_of_measure` weakened to `semiRingOfSetsType`
- in `ereal.v`:
  + lemmas `abse_ge0`, `gee0_abs`, `gte0_abs`, `lee0_abs`, `lte0_abs`,
    `mulN1e`, `muleN1` are generalized from `realDomainType` to
    `numDomainType`
- moved from `normedtype.v` to `mathcomp_extra.v`:
  + lemmas `ler_addgt0Pr`, `ler_addgt0Pl`, `in_segment_addgt0Pr`, `in_segment_addgt0Pl`,
- moved from `posnum.v` to `mathcomp_extra.v`:
  + lemma `splitr`
- moved from `measure.v` to `sequences.v`
  + lemma `cvg_geometric_series_half`
  + lemmas `realDe`, `realDed`, `realMe`, `nadde_eq0`, `padde_eq0`,
    `adde_ss_eq0`, `ndadde_eq0`, `pdadde_eq0`, `dadde_ss_eq0`,
    `mulrpinfty_real`, `mulpinftyr_real`, `mulrninfty_real`,
    `mulninftyr_real`, `mulrinfty_real`
- moved from `topology.v` to `functions.v`
  + section `function_space` (defintion `cst`, definition `fct_zmodMixin`,
    canonical `fct_zmodType`, definition `fct_ringMixin`, canonical `fct_ringType`,
    canonical `fct_comRingType`, definition `fct_lmodMixin`, canonical `fct_lmodType`,
    lemma `fct_lmodType`)
  + lemmas `addrfunE`, `opprfunE`, `mulrfunE`, `scalrfunE`, `cstE`, `exprfunE`, `compE`
  + definition `fctE`
- moved from `classical_sets.v` to `functions.v`
  + definition `patch`,	notation `restrict` and `f \_ D`

### Renamed

- in `topology.v`:
  + `closedC` -> `open_closedC`
  + `openC` -> `closed_openC`
  + `cvg_restrict_dep` -> `cvg_sigL`
- in `classical_sets.v`:
  + `mkset_nil` -> `set_nil`
- in `cardinality.v`:
  + `card_le0x` -> `card_ge0`
  + `card_eq_sym` -> `card_esym`
  + `set_finiteP` -> `finite_setP`
  + `set_finite0` -> `finite_set0`
  + `set_finite_seq` -> `finite_seq`
  + `set_finite_countable` -> `finite_set_countable`
  + `subset_set_finite` -> `sub_finite_set`
  + `set_finite_preimage` -> `finite_preimage`
  + `set_finite_diff` -> `finite_setD`
  + `countably_infinite_prod_nat` -> `card_nat2`
- file `csum.v` renamed to `esum.v` with the following renamings:
  + `\csum` -> `\esum`
  + `csum` -> `esum`
  + `csum0` -> `esum_set0`
  + `csum_ge0` -> `esum_ge0`
  + `csum_fset` -> `esum_fset`
  + `csum_image` -> `esum_image`
  + `csum_bigcup` -> `esum_bigcup`
- in `ereal.v`:
  + `lte_subl_addl` -> `lte_subel_addl`
  + `lte_subr_addr` -> `lte_suber_addr`
  + `lte_dsubl_addl` -> `lte_dsubel_addl`
  + `lte_dsubr_addr` -> `lte_dsuber_addr`

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`
  + lemmas `big_nat_widenl`, `big_geq_mkord`
- in `csum.v`:
  + lemmas `fsets_img`, `fsets_ord`, `fsets_ord_nat`, `fsets_ord_subset`, `csum_bigcup_le`,
    `le_csum_bigcup`
- in `classical_sets.v`:
  + lemma `subsetU`
  + definition `restrict_dep`, `extend_up`, lemma `restrict_depE`
- in `cardinality.v`:
  + lemma `surjective_image`, `surjective_image_eq0`
  + lemma `surjective_right_inverse`,
  + lemmas `card_le_surj`, `card_eq00`
  + lemmas `card_eqTT`, `card_eq_II`, `card_eq_le`, `card_leP`
  + lemmas `set_bijective_inverse`, `countable_trans`, `set_bijective_U1`,
    `set_bijective_cyclic_shift`, `set_bijective_cyclic_shift_simple`, `set_finite_bijective`,
    `subset_set_finite_card_le`, `injective_set_finite_card_le`, `injective_set_finite`,
    `injective_card_le`, `surjective_set_finite_card_le`, `set_finite_inter_set0_union`,
    `ex_in_D`.
  + definitions `min_of_D`, `min_of_D_seq`, `infsub_enum`
  + lemmas `min_of_D_seqE`, `increasing_infsub_enum`, `sorted_infsub_enum`, `injective_infsub_enum`,
    `subset_infsub_enum`, `infinite_nat_subset_countable`
  + definition `enumeration`
  + lemmas `enumeration_id`, `enumeration_set0`, `ex_enum_notin`
  + defnitions `min_of_e`, `min_of_e_seq`, `smallest_of_e`, `enum_wo_rep`
  + lemmas `enum_wo_repE`, `min_of_e_seqE`,
    `smallest_of_e_notin_enum_wo_rep`, `injective_enum_wo_rep`, `surjective_enum_wo_rep`,
    `set_bijective_enum_wo_rep`, `enumeration_enum_wo_rep`, `countable_enumeration`
  + definition `nat_of_pair`
  + lemmas `nat_of_pair_inj`, `countable_prod_nat`
- in `measure.v`:
  + definition `diff_fsets`
  + lemmas `semiRingOfSets_measurableI`, `semiRingOfSets_measurableD`, `semiRingOfSets_diff_fsetsE`,
    `semiRingOfSets_diff_fsets_disjoint`
  + definition `uncurry`
- in `sequences.v`:
  + lemmas `leq_fact`, `prod_rev`, `fact_split` (now in MathComp)
- in `boolp.v`
  + module BoolQuant with notations `` `[forall x P] `` and `` `[exists x P] ``
    (subsumed by `` `[< >] ``)
  + definition `xchooseb`
  + lemmas `existsPP`, `forallPP`, `existsbP`, `forallbP`, `forallbE`,
    `existsp_asboolP`, `forallp_asboolP`, `xchoosebP`, `imsetbP`
- in `normedtype.v`:
  + lemmas `nbhs_pinfty_gt_pos`, `nbhs_pinfty_ge_pos`, `nbhs_ninfty_lt_pos`,
    `nbhs_ninfty_le_pos`

## [0.3.13] - 2022-01-24

### Added

- in `topology.v`:
  + definitions `kolmogorov_space`, `accessible_space`
  + lemmas `accessible_closed_set1`, `accessible_kolmogorov`
  + lemma `filter_pair_set`
  + definition `prod_topo_apply`
  + lemmas `prod_topo_applyE`, `prod_topo_apply_continuous`, `hausdorff_product`
- in `ereal.v`:
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`
  + lemmas `mule_def_fin`, `mule_def_neq0_infty`, `mule_def_infty_neq0`, `neq0_mule_def`
  + notation `\-` in `ereal_scope` and `ereal_dual_scope`
  + lemma `fin_numB`
  + lemmas `mule_eq_pinfty`, `mule_eq_ninfty`
  + lemmas `fine_eq0`, `abse_eq0`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`

### Changed

- in `topology.v`:
  + renamed and generalized `setC_subset_set1C` implication to
    equivalence `subsetC1`
- in `ereal.v`:
  + lemmas `ereal_sup_gt`, `ereal_inf_lt` now use `exists2`
- notation `\*` moved from `realseq.v` to `topology.v`

### Renamed

- in `topology.v:
  + `hausdorff` -> `hausdorff_space`

### Removed

- in `realseq.v`:
  + notation `\-`

### Infrastructure

- add `.dir-locals.el` for company-coq symbols

## [0.3.12] - 2021-12-29

### Added

- in `boolp.v`:
  + lemmas `not_True`, `not_False`
- in `classical_sets.v`:
  + lemma `setDIr`
  + lemmas `setMT`, `setTM`, `setMI`
  + lemmas `setSM`, `setM_bigcupr`, `setM_bigcupl`
  + lemmas `cover_restr`, `eqcover_r`
  + lemma `notin_set`
- in `reals.v`:
  + lemma `has_ub_lbN`
- in `ereal.v`:
  + lemma `onee_eq0`
  + lemma `EFinB`
  + lemmas `mule_eq0`, `mule_lt0_lt0`, `mule_gt0_lt0`, `mule_lt0_gt0`,
    `pmule_rge0`, `pmule_lge0`, `nmule_lge0`, `nmule_rge0`,
    `pmule_rgt0`, `pmule_lgt0`, `nmule_lgt0`, `nmule_rgt0`
  + lemmas `muleBr`, `muleBl`
  + lemma `eqe_absl`
  + lemma `lee_pmul`
  + lemmas `fin_numElt`, `fin_numPlt`
- in `topology.v`
  + lemmas `cstE`, `compE`, `opprfunE`, `addrfunE`, `mulrfunE`, `scalrfunE`, `exprfunE`
  + multi-rule `fctE`
  + lemmas `within_interior`, `within_subset,` `withinE`, `fmap_within_eq`
  + definitions `subspace`, `incl_subspace`.
  + canonical instances of `pointedType`, `filterType`, `topologicalType`,
    `uniformType` and `pseudoMetricType` on `subspace`.
  + lemmas `nbhs_subspaceP`, `nbhs_subspace_in`, `nbhs_subspace_out`, `subspace_cvgP`,
    `subspace_continuousP`, `subspace_eq_continuous`,  `nbhs_subspace_interior`,
    `nbhs_subspace_ex`, `incl_subspace_continuous`, `open_subspace1out`,
    `open_subspace_out`, `open_subspaceT`, `open_subspaceIT`, `open_subspaceTI`,
    `closed_subspaceT`, `open_subspaceP`, `open_subspaceW`, `subspace_hausdorff`,
    and `compact_subspaceIP`.
- in `normedtype.v`
  + lemmas `continuous_shift`, `continuous_withinNshiftx`
  + lemmas `bounded_fun_has_ubound`, `bounded_funN`, `bounded_fun_has_lbound`,
    `bounded_funD`
- in `derive.v`
  + lemmas `derive1_comp`, `derivable_cst`, `derivable_id`, trigger_derive`
  + instances `is_derive_id`, `is_derive_Nid`
- in `sequences.v`:
  + lemmas `cvg_series_bounded`, `cvg_to_0_linear`, `lim_cvg_to_0_linear`.
  + lemma `cvg_sub0`
  + lemma `cvg_zero`
  + lemmas `ereal_cvg_abs0`, `ereal_cvg_sub0`, `ereal_squeeze`
  + lemma `ereal_is_cvgD`
- in `measure.v`:
  + hints for `measurable0` and `measurableT`
- file `realfun.v`:
  + lemma `is_derive1_caratheodory`, `is_derive_0_is_cst`
  + instance `is_derive1_comp`
  + lemmas `is_deriveV`, `is_derive_inverse`
- new file `nsatz_realType`
- new file `exp.v`
  + lemma `normr_nneg` (hint)
  + definitions `pseries`, `pseries_diffs`
  + facts `is_cvg_pseries_inside_norm`, `is_cvg_pseries_inside`
  + lemmas `pseries_diffsN`, `pseries_diffs_inv_fact`, `pseries_diffs_sumE`,
           `pseries_diffs_equiv`, `is_cvg_pseries_diffs_equiv`,
           `pseries_snd_diffs`
  + lemmas `expR0`, `expR_ge1Dx`, `exp_coeffE`, `expRE`
  + instance `is_derive_expR`
  + lemmas `derivable_expR`, `continuous_expR`, `expRxDyMexpx`, `expRxMexpNx_1`
  + lemmas `pexpR_gt1`, `expR_gt0`, `expRN`, `expRD`, `expRMm`
  + lemmas `expR_gt1`, `expR_lt1`, `expRB`, `ltr_expR`, `ler_expR`, `expR_inj`,
    `expR_total_gt1`, `expR_total`
  + definition `ln`
  + fact `ln0`
  + lemmas `expK`, `lnK`, `ln1`, `lnM`, `ln_inj`, `lnV`, `ln_div`, `ltr_ln`, `ler_ln`, `lnX`
  + lemmas `le_ln1Dx`, `ln_sublinear`, `ln_ge0`, `ln_gt0`
  + lemma `continuous_ln`
  + instance `is_derive1_ln`
  + definition `exp_fun`, notation `` `^ ``
  + lemmas `exp_fun_gt0`, `exp_funr1`, `exp_funr0`, `exp_fun1`, `ler_exp_fun`,
    `exp_funD`, `exp_fun_inv`, `exp_fun_mulrn`
  + definition `riemannR`, lemmas `riemannR_gt0`, `dvg_riemannR`
- new file `trigo.v`
  + lemmas `sqrtvR`, `eqr_div`, `big_nat_mul`, `cvg_series_cvg_series_group`,
    `lt_sum_lim_series`
  + definitions `periodic`, `alternating`
  + lemmas `periodicn`, `alternatingn`
  + definition `sin_coeff`
  + lemmas `sin_coeffE`, `sin_coeff_even`, `is_cvg_series_sin_coeff`
  + definition `sin`
  + lemmas `sinE`
  + definition `sin_coeff'`
  + lemmas `sin_coeff'E`, `cvg_sin_coeff'`, `diffs_sin`, `series_sin_coeff0`, `sin0`
  + definition `cos_coeff`
  + lemmas `cos_ceff_2_0`, `cos_coeff_2_2`, `cos_coeff_2_4`, `cos_coeffE`, `is_cvg_series_cos_coeff`
  + definition `cos`
  + lemma `cosE`
  + definition `cos_coeff'`
  + lemmas `cos_coeff'E`, `cvg_cos_coeff'`, `diffs_cos`, `series_cos_coeff0`, `cos0`
  + instance `is_derive_sin`
  + lemmas `derivable_sin`, `continuous_sin`, `is_derive_cos`, `derivable_cos`, `continuous_cos`
  + lemmas `cos2Dsin2`, `cos_max`, `cos_geN1`, `cos_le1`, `sin_max`, `sin_geN1`, `sin_le1`
  + fact `sinD_cosD`
  + lemmas `sinD`, `cosD`
  + lemmas `sin2cos2`, `cos2sin2`, `sin_mulr2n`, `cos_mulr2n`
  + fact `sinN_cosN`
  + lemmas `sinN`, `cosN`
  + lemmas `sin_sg`, `cos_sg`, `cosB`, `sinB`
  + lemmas `norm_cos_eq1`, `norm_sin_eq1`, `cos1sin0`, `sin0cos1`, `cos_norm`
  + definition `pi`
  + lemmas `pihalfE`, `cos2_lt0`, `cos_exists`
  + lemmas `sin2_gt0`, `cos_pihalf_uniq`, `pihalf_02_cos_pihalf`, `pihalf_02`, `pi_gt0`, `pi_ge0`
  + lemmas `sin_gt0_pihalf`, `cos_gt0_pihalf`, `cos_pihalf`, `sin_pihalf`, `cos_ge0_pihalf`, `cospi`, `sinpi`
  + lemmas `cos2pi`, `sin2pi`, `sinDpi`, `cosDpi`, `sinD2pi`, `cosD2pi`
  + lemmas `cosDpihalf`, `cosBpihalf`, `sinDpihalf`, `sinBpihalf`, `sin_ge0_pi`
  + lemmas `ltr_cos`, `ltr_sin`, `cos_inj`, `sin_inj`
  + definition `tan`
  + lemmas `tan0`, `tanpi`, `tanN`, `tanD`, `tan_mulr2n`, `cos2_tan2`
  + lemmas `tan_pihalf`, `tan_piquarter`, `tanDpi`, `continuous_tan`
  + lemmas `is_derive_tan`, `derivable_tan`, `ltr_tan`, `tan_inj`
  + definition `acos`
  + lemmas `acos_def`, `acos_ge0`, `acos_lepi`, `acosK`, `acos_gt0`, `acos_ltpi`
  + lemmas `cosK`, `sin_acos`, `continuous_acos`, `is_derive1_acos`
  + definition `asin`
  + lemmas `asin_def`, `asin_geNpi2`, `asin_lepi2`, `asinK`, `asin_ltpi2`, `asin_gtNpi2`
  + lemmas `sinK`, `cos_asin`, `continuous_asin`, `is_derive1_asin`
  + definition `atan`
  + lemmas `atan_def`, `atan_gtNpi2`, `atan_ltpi2`, `atanK`, `tanK`
  + lemmas `continuous_atan`, `cos_atan`
  + instance `is_derive1_atan`

### Changed

- in `normedtype.v`:
  + `nbhs_minfty_lt` renamed to `nbhs_ninfty_lt_pos` and changed to not use `{posnum R}`
  + `nbhs_minfty_le` renamed to `nbhs_ninfty_le_pos` and changed to not use `{posnum R}`
- in `sequences.v`:
  + lemma `is_cvg_ereal_nneg_natsum`: remove superfluous `P` parameter
  + statements of lemmas `nondecreasing_cvg`, `nondecreasing_is_cvg`,
    `nonincreasing_cvg`, `nonincreasing_is_cvg` use `has_{l,u}bound`
    predicates instead of requiring an additional variable
  + statement of lemma `S1_sup` use `ubound` instead of requiring an
    additional variable

### Renamed

- in `normedtype.v`:
  + `nbhs_minfty_lt_real` -> `nbhs_ninfty_lt`
  + `nbhs_minfty_le_real` -> `nbhs_ninfty_le`
- in `sequences.v`:
  + `cvgNminfty` -> `cvgNninfty`
  + `cvgPminfty` -> `cvgPninfty`
  + `ler_cvg_minfty` -> `ler_cvg_ninfty`
  + `nondecreasing_seq_ereal_cvg` -> `ereal_nondecreasing_cvg`
- in `normedtype.v`:
  + `nbhs_pinfty_gt` -> `nbhs_pinfty_gt_pos`
  + `nbhs_pinfty_ge` -> `nbhs_pinfty_ge_pos`
  + `nbhs_pinfty_gt_real` -> `nbhs_pinfty_gt`
  + `nbhs_pinfty_ge_real` -> `nbhs_pinfty_ge`
- in `measure.v`:
  + `measure_bigcup` -> `measure_bigsetU`
- in `ereal.v`:
  + `mulrEDr` -> `muleDr`
  + `mulrEDl` -> `muleDl`
  + `dmulrEDr` -> `dmuleDr`
  + `dmulrEDl` -> `dmuleDl`
  + `NEFin` -> `EFinN`
  + `addEFin` -> `EFinD`
  + `mulEFun` -> `EFinM`
  + `daddEFin` -> `dEFinD`
  + `dsubEFin` -> `dEFinB`

### Removed

- in `ereal.v`:
  + lemma `subEFin`

### Infrastructure

- in `Makefile.common`
  + add `doc` and `doc-clean` targets

## [0.3.11] - 2021-11-14

### Added

- in `boolp.v`:
  + lemmas `orA`, `andA`
- in `classical_sets.v`
  + lemma `setC_inj`,
  + lemma `setD1K`,
  + lemma `subTset`,
  + lemma `setUidPr`, `setUidl` and `setUidr`,
  + lemma `setIidPr`, `setIidl` and `setIidr`,
  + lemma `set_fset0`, `set_fset1`, `set_fsetI`, `set_fsetU`,
  + lemma `bigcap_inf`, `subset_bigcup_r`, `subset_bigcap_r`,
    `eq_bigcupl`, `eq_bigcapl`, `eq_bigcup`, `eq_bigcap`, `bigcupU`,
    `bigcapI`, `bigcup_const`, `bigcap_const`, `bigcapIr`, `bigcupUr`,
    `bigcap_set0`, `bigcap_set1`, `bigcap0`, `bigcapT`, `bigcupT`,
    `bigcapTP`, `setI_bigcupl`, `setU_bigcapl`, `bigcup_mkcond`,
    `bigcap_mkcond`, `setC_bigsetU`, `setC_bigsetI`,
    `bigcap_set_cond`, `bigcap_set`, `bigcap_split`, `bigcap_mkord`,
    `subset_bigsetI`, `subset_bigsetI_cond`, `bigcap_image`
  + lemmas `bigcup_setU1`, `bigcap_setU1`, `bigcup_setU`,
    `bigcap_setU`, `bigcup_fset`, `bigcap_fset`, `bigcup_fsetU1`,
    `bigcap_fsetU1`, `bigcup_fsetD1`, `bigcap_fsetD1`,
  + definition `mem_set : A u -> u \in A`
  + lemmas `in_setP` and `in_set2P`
  + lemma `forall_sig`
  + definition `patch`, notation `restrict` and `f \_ D`, definitions
    `restrict_dep` and `extend_dep`, with lemmas `restrict_depE`,
    `fun_eq_inP`, `extend_restrict_dep`, `extend_depK`,
    `restrict_extend_dep`, `restrict_dep_restrict`,
    `restrict_dep_setT`
  + lemmas `setUS`, `setSU`, `setUSS`, `setUCA`, `setUAC`, `setUACA`,
    `setUUl`, `setUUr`
  + lemmas `bigcup_image`, `bigcup_of_set1`, `set_fset0`, `set_fset1`, `set_fsetI`,
    `set_fsetU`, `set_fsetU1`, `set_fsetD`, `set_fsetD1`,
  + notation `` [set` i] ``
  + notations `set_itv`, `` `[a, b] ``, `` `]a, b] ``, `` `[a, b[ ``,
    `` `]a, b[ ``, `` `]-oo, b] ``, `` `]-oo, b[ ``, `` `[a, +oo] ``,
    `` `]a, +oo] ``, `` `]-oo, +oo[ ``
  + lemmas `setDDl`, `setDDr`
- in `topology.v`:
  + lemma `fmap_comp`
  + definition `finSubCover`
  + notations ``{uniform` A -> V }`` and `{uniform U -> V}` and their
    canonical structures of uniform type.
  + definition `uniform_fun` to cast into
  + notations `{uniform A, F --> f }` and `{uniform, F --> f}`
  + lemma `uniform_cvgE`
  + lemma `uniform_nbhs`
  + notation `{ptws U -> V}` and its canonical structure of
    topological type,
  + definition `ptws_fun`
  + notation `{ptws F --> f }`
  + lemma `ptws_cvgE`
  + lemma `ptws_uniform_cvg`
  + lemma `cvg_restrict_dep`
  + lemma `eq_in_close`
  + lemma `hausdorrf_close_eq_in`
  + lemma `uniform_subset_nbhs`
  + lemma `uniform_subset_cvg`
  + lemma `uniform_restrict_cvg`
  + lemma `cvg_uniformU`
  + lemma `cvg_uniform_set0`
  + notation `{family fam, U -> V}` and its canonical structure of
    topological type
  + notation `{family fam, F --> f}`
  + lemma `fam_cvgP`
  + lemma `fam_cvgE`
  + definition `compactly_in`
  + lemma `family_cvg_subset`
  + lemma `family_cvg_finite_covers`
  + lemma `compact_cvg_within_compact`
  + lemma `le_bigmax`
  + definition `monotonous`
  + lemma `and_prop_in`
  + lemmas `mem_inc_segment`, `mem_dec_segment`
  + lemmas `ltr_distlC`, `ler_distlC`
  + lemmas `subset_ball_prop_in_itv`, `subset_ball_prop_in_itvcc`
  + lemma `dense_rat`
- in `normedtype.v`:
  + lemma `is_intervalPlt`
  + lemma `mule_continuous`
  + lemmas `ereal_is_cvgN`, `ereal_cvgZr`, `ereal_is_cvgZr`, `ereal_cvgZl`, `ereal_is_cvgZl`,
    `ereal_limZr`, `ereal_limZl`, `ereal_limN`
  + lemma `bound_itvE`
  + lemmas `nearN`, `near_in_itv`
  + lemmas `itvxx`, `itvxxP`, `subset_itv_oo_cc`
  + lemma `at_right_in_segment`
  + notations ``f @`[a, b]``, ``g @`]a , b[``
  + lemmas `mono_mem_image_segment`, `mono_mem_image_itvoo`, `mono_surj_image_segment`,
    `inc_segment_image`, `dec_segment_image`, `inc_surj_image_segment`, `dec_surj_image_segment`,
    `inc_surj_image_segmentP`, `dec_surj_image_segmentP`, ``mono_surj_image_segmentP``
- in `reals.v`:
  + lemmas `floor1`, `floor_neq0`
  + lemma `int_lbound_has_minimum`
  + lemma `rat_in_itvoo`
- in `ereal.v`:
  + notation `x +? y` for `adde_def x y`
  + lemmas `ge0_adde_def`, `onee_neq0`, `mule0`, `mul0e`
  + lemmas `mulrEDr`, `mulrEDl`, `ge0_muleDr`, `ge0_muleDl`
  + lemmas `ge0_sume_distrl`, `ge0_sume_distrr`
  + lemmas `mulEFin`, `mule_neq0`, `mule_ge0`, `muleA`
  + lemma `muleE`
  + lemmas `muleN`, `mulNe`, `muleNN`, `gee_pmull`, `lee_mul01Pr`
  + lemmas `lte_pdivr_mull`, `lte_pdivr_mulr`, `lte_pdivl_mull`, `lte_pdivl_mulr`,
    `lte_ndivl_mulr`, `lte_ndivl_mull`, `lte_ndivr_mull`, `lte_ndivr_mulr`
  + lemmas `lee_pdivr_mull`, `lee_pdivr_mulr`, `lee_pdivl_mull`, `lee_pdivl_mulr`,
    `lee_ndivl_mulr`, `lee_ndivl_mull`, `lee_ndivr_mull`, `lee_ndivr_mulr`
  + lemmas `mulrpinfty`, `mulrninfty`, `mulpinftyr`, `mulninftyr`, `mule_gt0`
  + definition `mulrinfty`
  + lemmas `mulN1e`, `muleN1`
  + lemmas `mule_ninfty_pinfty`, `mule_pinfty_ninfty`, `mule_pinfty_pinfty`
  + lemmas `mule_le0_ge0`, `mule_ge0_le0`, `pmule_rle0`, `pmule_lle0`,
    `nmule_lle0`, `nmule_rle0`
  + lemma `sube0`
  + lemmas `adde_le0`, `sume_le0`, `oppe_ge0`, `oppe_le0`,
    `lte_opp`, `gee_addl`, `gee_addr`, `lte_addr`,
    `gte_subl`, `gte_subr`, `lte_le_sub`, `lee_sum_npos_subset`,
    `lee_sum_npos`, `lee_sum_npos_ord`, `lee_sum_npos_natr`,
    `lee_sum_npos_natl`, `lee_sum_npos_subfset`, `lee_opp`,
    `le0_muleDl`, `le0_muleDr`, `le0_sume_distrl`, `le0_sume_distrr`,
    `adde_defNN`, `minEFin`, `mine_ninftyl`, `mine_ninftyr`, `mine_pinftyl`,
    `mine_pinftyr`, `oppe_max`, `oppe_min`, `mineMr`, `mineMl`
  + definitions `dual_adde`
  + notations for the above in scope `ereal_dual_scope` delimited by `dE`
  + lemmas `dual_addeE`, `dual_sumeE`, `dual_addeE_def`, `daddEFin`,
    `dsumEFin`, `dsubEFin`, `dadde0`, `dadd0e`, `daddeC`, `daddeA`,
    `daddeAC`, `daddeCA`, `daddeACA`, `doppeD`, `dsube0`, `dsub0e`, `daddeK`,
    `dfin_numD`, `dfineD`, `dsubeK`, `dsube_eq`,
    `dsubee`, `dadde_eq_pinfty`, `daddooe`, `dadde_Neq_pinfty`,
    `dadde_Neq_ninfty`, `desum_fset_pinfty`, `desum_pinfty`,
    `desum_fset_ninfty`, `desum_ninfty`, `dadde_ge0`, `dadde_le0`,
    `dsume_ge0`, `dsume_le0`, `dsube_lt0`, `dsubre_le0`,
    `dsuber_le0`, `dsube_ge0`, `lte_dadd`, `lee_daddl`, `lee_daddr`,
    `gee_daddl`, `gee_daddr`, `lte_daddl`, `lte_daddr`, `gte_dsubl`,
    `gte_dsubr`, `lte_dadd2lE`, `lee_dadd2l`, `lee_dadd2lE`,
    `lee_dadd2r`, `lee_dadd`, `lte_le_dadd`, `lee_dsub`,
    `lte_le_dsub`, `lee_dsum`, `lee_dsum_nneg_subset`,
    `lee_dsum_npos_subset`, `lee_dsum_nneg`, `lee_dsum_npos`,
    `lee_dsum_nneg_ord`, `lee_dsum_npos_ord`, `lee_dsum_nneg_natr`,
    `lee_dsum_npos_natr`, `lee_dsum_nneg_natl`, `lee_dsum_npos_natl`,
    `lee_dsum_nneg_subfset`, `lee_dsum_npos_subfset`,
    `lte_dsubl_addr`, `lte_dsubl_addl`, `lte_dsubr_addr`,
    `lee_dsubr_addr`, `lee_dsubl_addr`, `ge0_dsume_distrl`, `dmulrEDr`,
    `dmulrEDl`, `dge0_mulreDr`, `dge0_mulreDl`, `dle0_mulreDr`, `dle0_mulreDl`,
    `ge0_dsume_distrr`, `le0_dsume_distrl`, `le0_dsume_distrr`,
    `lee_abs_dadd`, `lee_abs_dsum`, `lee_abs_dsub`, `dadde_minl`, `dadde_minr`,
    `lee_dadde`, `lte_spdaddr`
  + lemmas `abse0`, `abse_ge0`, `lee_abs`, `abse_id`, `lee_abs_add`, `lee_abs_sum`,
    `lee_abs_sub`, `gee0_abs`, `gte0_abs`, `lee_abs`, `lte0_abs`, `abseM`, `lte_absl`,
    `eqe_absl`
  + notations `maxe`, `mine`
  + lemmas `maxEFin`, `adde_maxl`, `adde_maxr`,
    `maxe_pinftyl`, `maxe_pinftyr`, `maxe_ninftyl`, `maxe_ninftyr`
  + lemmas `sub0e`, `lee_wpmul2r`, `mule_ninfty_ninfty`
  + lemmas `sube_eq` `lte_pmul2r`, `lte_pmul2l`, `lte_nmul2l`, `lte_nmul2r`, `mule_le0`,
    `pmule_llt0`, `pmule_rlt0`, `nmule_llt0`, `nmule_rlt0`, `mule_lt0`
  + lemmas `maxeMl`, `maxeMr`
  + lemmas `lte_0_pinfty`, `lte_ninfty_0`, `lee_0_pinfty`, `lee_ninfty_0`,
    `oppe_gt0`, `oppe_lt0`
  + lemma `telescope_sume`
  + lemmas `lte_add_pinfty`, `lte_sum_pinfty`
- in `cardinality.v`:
  + definition `nat_of_pair`, lemma `nat_of_pair_inj`
  + lemmas `surjectiveE`, `surj_image_eq`, `can_surjective`
- in `sequences.v`:
  + lemmas `lt_lim`, `nondecreasing_dvg_lt`, `ereal_lim_sum`
  + lemmas `ereal_nondecreasing_opp`, `ereal_nondecreasing_is_cvg`, `ereal_nonincreasing_cvg`,
    `ereal_nonincreasing_is_cvg`
- file `realfun.v`:
  + lemmas `itv_continuous_inj_le`, `itv_continuous_inj_ge`, `itv_continuous_inj_mono`
  + lemmas `segment_continuous_inj_le`, `segment_continuous_inj_ge`,
    `segment_can_le`, `segment_can_ge`, `segment_can_mono`
  + lemmas `segment_continuous_surjective`, `segment_continuous_le_surjective`,
    `segment_continuous_ge_surjective`
  + lemmas `continuous_inj_image_segment`, `continuous_inj_image_segmentP`,
    `segment_continuous_can_sym`, `segment_continuous_le_can_sym`, `segment_continuous_ge_can_sym`,
    `segment_inc_surj_continuous`, `segment_dec_surj_continuous`, `segment_mono_surj_continuous`
  + lemmas `segment_can_le_continuous`, `segment_can_ge_continuous`, `segment_can_continuous`
  + lemmas `near_can_continuousAcan_sym`, `near_can_continuous`, `near_continuous_can_sym`
  + lemmas `exp_continuous`, `sqr_continuous`, `sqrt_continuous`.
- in `measure.v`:
  + definition `seqDU`
  + lemmas `trivIset_seqDU`, `bigsetU_seqDU`, `seqDU_bigcup_eq`, `seqDUE`
  + lemmas `bigcup_measurable`, `bigcap_measurable`, `bigsetI_measurable`

### Changed

- in `classical_sets.v`
  + `setU_bigcup` -> `bigcupUl` and reversed
  + `setI_bigcap` -> `bigcapIl` and reversed
  + removed spurious disjunction in `bigcup0P`
  + `bigcup_ord` -> `bigcup_mkord` and reversed
  + `bigcup_of_set1` -> `bigcup_imset1`
  + `bigcupD1` -> `bigcup_setD1` and `bigcapD1` -> `bigcap_setD1` and
    rephrased using ``P `\ x`` instead of ``P `&` ~` [set x]``
  + order of arguments for `setIS`, `setSI`, `setUS`, `setSU`, `setSD`, `setDS`
  + generalize lemma `perm_eq_trivIset`
- in `topology.v`:
  + replace `closed_cvg_loc` and `closed_cvg` by a more general lemma `closed_cvg`
- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`
  + definition `is_interval`
  + the following lemmas have been generalized to `orderType`,
    renamed as follows, moved out of the module `BigmaxBigminr`
    to `topology.v`:
    * `bigmaxr_mkcond` -> `bigmax_mkcond`
    * `bigmaxr_split` -> `bigmax_split`
    * `bigmaxr_idl` -> `bigmax_idl`
    * `bigmaxrID` -> `bigmaxID`
    * `bigmaxr_seq1` -> `bigmax_seq1`
    * `bigmaxr_pred1_eq` -> `bigmax_pred1_eq`
    * `bigmaxr_pred1` -> `bigmax_pred1`
    * `bigmaxrD1` -> `bigmaxD1`
    * `ler_bigmaxr_cond`  -> `ler_bigmax_cond `
    * `ler_bigmaxr` -> `ler_bigmax`
    * `bigmaxr_lerP` -> `bigmax_lerP`
    * `bigmaxr_sup` -> `bigmax_sup`
    * `bigmaxr_ltrP` -> `bigmax_ltrP`
    * `bigmaxr_gerP` -> `bigmax_gerP`
    * `bigmaxr_eq_arg` -> `bigmax_eq_arg`
    * `bigmaxr_gtrP` -> `bigmax_gtrP`
    * `eq_bigmaxr` -> `eq_bigmax`
    * module `BigmaxBigminr` -> `Bigminr`
- in `ereal.v`:
  + change definition `mule` such that 0 x oo = 0
  + `adde` now defined using `nosimpl` and `adde_subdef`
  + `mule` now defined using `nosimpl` and `mule_subdef`
  + lemmas `lte_addl`, `lte_subl_addr`, `lte_subl_addl`, `lte_subr_addr`,
    `lte_subr_addr`, `lte_subr_addr`, `lb_ereal_inf_adherent`
  + `oppeD` to use `fin_num`
  + weaken `realDomainType` to `numDomainType` in `mule_ninfty_pinfty`,
    `mule_pinfty_ninfty`, `mule_pinfty_pinfty`, `mule_ninfty_ninfty`,
    `mule_neq0`, `mule_ge0`, `mule_le0`, `mule_gt0`, `mule_le0_ge0`,
    `mule_ge0_le0`
- in `reals.v`:
  + generalize from `realType` to `realDomainType` lemmas
    `has_ub_image_norm`, `has_inf_supN`
- in `sequences.v`:
  + generalize from `realType` to `realFieldType` lemmas
    `cvg_has_ub`, `cvg_has_sup`, `cvg_has_inf`
  + change the statements of `cvgPpinfty`, `cvgPminfty`,
    `cvgPpinfty_lt`
  + generalize `nondecreasing_seqP`, `nonincreasing_seqP`, `increasing_seqP`,
    `decreasing_seqP` to equivalences
  + generalize `lee_lim`, `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`,
    `ereal_cvgD`, `ereal_limD`, `ereal_pseries0`, `eq_ereal_pseries` from `realType` to `realFieldType`
  + lemma `ereal_pseries_pred0` moved from `csum.v`, minor generalization
- in `landau.v`:
  + lemma `cvg_shift` renamed to `cvg_comp_shift` and moved to `normedtype.v`
- in `measure.v`:
  + lemmas `measureDI`, `measureD`, `sigma_finiteP`
- `exist_congr` -> `eq_exist` and moved from `classsical_sets.v` to
  `boolp.v`
- `predeqP` moved from `classsical_sets.v` to `boolp.v`
- moved from `landau.v` to `normedtype.v`:
  + lemmas `comp_shiftK`, `comp_centerK`, `shift0`, `center0`, `near_shift`,
    `cvg_shift`
- lemma `exists2P` moved from `topology.v` to `boolp.v`
- move from `sequences.v` to `normedtype.v` and generalize from `nat` to `T : topologicalType`
  + lemmas `ereal_cvgN`

### Renamed

- in `classical_sets.v`
  + `eqbigcup_r` -> `eq_bigcupr`
  + `eqbigcap_r` -> `eq_bigcapr`
  + `bigcup_distrr` -> `setI_bigcupr`
  + `bigcup_distrl` -> `setI_bigcupl`
  + `bigcup_refl` -> `bigcup_splitn`
  + `setMT` -> `setMTT`
- in `ereal.v`:
  + `adde` -> `adde_subdef`
  + `mule` -> `mule_subdef`
  + `real_of_extended` -> `fine`
  + `real_of_extendedN` -> `fineN`
  + `real_of_extendedD` -> `fineD`
  + `EFin_real_of_extended` -> `fineK`
  + `real_of_extended_expand` -> `fine_expand`
- in `sequences.v`:
  + `nondecreasing_seq_ereal_cvg` -> `nondecreasing_ereal_cvg`
- in `topology.v`:
  + `nbhs'` -> `dnbhs`
  + `nbhsE'` -> `dnbhs`
  + `nbhs'_filter` -> `dnbhs_filter`
  + `nbhs'_filter_on` -> `dnbhs_filter_on`
  + `nbhs_nbhs'` -> `nbhs_dnbhs`
  + `Proper_nbhs'_regular_numFieldType` -> `Proper_dnbhs_regular_numFieldType`
  + `Proper_nbhs'_numFieldType` -> `Proper_dnbhs_numFieldType`
  + `ereal_nbhs'` -> `ereal_dnbhs`
  + `ereal_nbhs'_filter` -> `ereal_dnbhs_filter`
  + `ereal_nbhs'_le` -> `ereal_dnbhs_le`
  + `ereal_nbhs'_le_finite` -> `ereal_dnbhs_le_finite`
  + `Proper_nbhs'_numFieldType` -> `Proper_dnbhs_numFieldType`
  + `Proper_nbhs'_realType` -> `Proper_dnbhs_realType`
  + `nbhs'0_lt` -> `dnbhs0_lt`
  + `nbhs'0_le` -> `dnbhs0_le`
  + `continuity_pt_nbhs'` -> `continuity_pt_dnbhs`
- in `measure.v`:
  + `measure_additive2` -> `measureU`
  + `measure_additive` -> `measure_bigcup`

### Removed

- in `boolp.v`:
  + definition `PredType`
  + local notation `predOfType`
- in `nngnum.v`:
  + module `BigmaxrNonneg` containing the following lemmas:
    * `bigmaxr_mkcond`, `bigmaxr_split`, `bigmaxr_idl`, `bigmaxrID`,
      `bigmaxr_seq1`, `bigmaxr_pred1_eq`, `bigmaxr_pred1`, `bigmaxrD1`,
      `ler_bigmaxr_cond`, `ler_bigmaxr`, `bigmaxr_lerP`, `bigmaxr_sup`,
      `bigmaxr_ltrP`, `bigmaxr_gerP`, `bigmaxr_gtrP`
- in `sequences.v`:
  + lemma `closed_seq`
- in `normedtype.v`:
  + lemma `is_intervalPle`
- in `topology.v`:
  + lemma `continuous_cst`
  + definition `cvg_to_locally`
- in `csum.v`:
  + lemma `ub_ereal_sup_adherent_img`

## [0.3.10] - 2021-08-11

### Added

- in `classical_sets.v`:
  + lemmas `bigcup_image`, `bigcup_of_set1`
  + lemmas `bigcupD1`, `bigcapD1`
- in `boolp.v`:
  + definitions `equality_mixin_of_Type`, `choice_of_Type`
- in `normedtype.v`:
  + lemma `cvg_bounded_real`
  + lemma `pseudoMetricNormedZModType_hausdorff`
- in `sequences.v`:
  + lemmas `seriesN`, `seriesD`, `seriesZ`, `is_cvg_seriesN`, `lim_seriesN`,
    `is_cvg_seriesZ`, `lim_seriesZ`, `is_cvg_seriesD`, `lim_seriesD`,
    `is_cvg_seriesB`, `lim_seriesB`, `lim_series_le`, `lim_series_norm`
- in `measure.v`:
  + HB.mixin `AlgebraOfSets_from_RingOfSets`
  + HB.structure `AlgebraOfSets` and notation `algebraOfSetsType`
  + HB.instance `T_isAlgebraOfSets` in HB.builders `isAlgebraOfSets`
  + lemma `bigcup_set_cond`
  + definition `measurable_fun`
  + lemma `adde_undef_nneg_series`
  + lemma `adde_def_nneg_series`
  + lemmas `cvg_geometric_series_half`, `epsilon_trick`
  + definition `measurable_cover`
  + lemmas `cover_measurable`, `cover_subset`
  + definition `mu_ext`
  + lemmas `le_mu_ext`, `mu_ext_ge0`, `mu_ext0`, `measurable_uncurry`,
    `mu_ext_sigma_subadditive`
  + canonical `outer_measure_of_measure`

### Changed

- in `ereal.v`, definition `adde_undef` changed to `adde_def`
  + consequently, the following lemmas changed:
    * in `ereal.v`, `adde_undefC` renamed to `adde_defC`,
      `fin_num_adde_undef` renamed to `fin_num_adde_def`
    * in `sequences.v`, `ereal_cvgD` and `ereal_limD` now use hypotheses with `adde_def`
- in `sequences.v`:
  + generalize `{in,de}creasing_seqP`, `non{in,de}creasing_seqP` from `numDomainType`
    to `porderType`
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
- in `measure.v`:
  + generalize lemma `eq_bigcupB_of`
  + HB.mixin `Measurable_from_ringOfSets` changed to `Measurable_from_algebraOfSets`
  + HB.instance `T_isRingOfSets` becomes `T_isAlgebraOfSets` in HB.builders `isMeasurable`
  + lemma `measurableC` now applies to `algebraOfSetsType` instead of `measureableType`
- moved from `normedtype.v` to `reals.v`:
  + lemmas `inf_lb_strict`, `sup_ub_strict`
- moved from `sequences.v` to `reals.v`:
  + lemma `has_ub_image_norm`

### Renamed

- in `classical_sets.v`:
  + `bigcup_mkset` -> `bigcup_set`
  + `bigsetU` -> `bigcup`
  + `bigsetI` -> `bigcap`
  + `trivIset_bigUI` -> `trivIset_bigsetUI`
- in `measure.v`:
  + `isRingOfSets` -> `isAlgebraOfSets`
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

## [0.3.9] - 2021-06-12

### Added

- in `sequences.v`:
  + lemma `dvg_harmonic`
- in `classical_sets.v`:
  + definitions `image`, `image2`

### Changed

- in `classical_sets.v`
  + notations `[set E | x in A]` and `[set E | x in A & y in B]`
    now use definitions `image` and `image2` resp.
  + notation ``f @` A`` now uses the definition `image`
  + the order of arguments of `image` has changed compared to version 0.3.7:
    it is now `image A f` (it used to be `image f A`)

### Removed

- in `sequences.v`:
  + lemma `iter_addr`

## [0.3.8] - 2021-06-01

### Added

- file `reals.v`:
  + lemmas `le_floor`, `le_ceil`
- in `ereal.v`:
  + lemmas `big_nat_widenl`, `big_geq_mkord`
  + lemmas `lee_sum_nneg_natr`, `lee_sum_nneg_natl`
  + lemmas `ereal_sup_gt`, `ereal_inf_lt`
  + notation `0`/`1` for `0%R%:E`/`1%R:%E` in `ereal_scope`
- in `classical_sets.v`
  + lemma `subset_bigsetU_cond`
  + lemma `eq_imagel`
- in `sequences.v`:
  + notations `\sum_(i <oo) F i`
  + lemmas `ereal_pseries_sum_nat`, `lte_lim`
  + lemmas `is_cvg_ereal_nneg_natsum_cond`, `is_cvg_ereal_nneg_natsum`
  + lemma `ereal_pseriesD`, `ereal_pseries0`, `eq_ereal_pseries`
  + lemmas `leq_fact`, `prod_rev`, `fact_split`
  + definition `exp_coeff`
  + lemmas `exp_coeff_ge0`, `series_exp_coeff0`, `is_cvg_series_exp_coeff_pos`,
    ` normed_series_exp_coeff`, `is_cvg_series_exp_coeff `, `cvg_exp_coeff`
  + definition `expR`
- in `measure.v`:
  + lemma `eq_bigcupB_of_bigsetU`
  + definitions `caratheodory_type`
  + definition `caratheodory_measure` and lemma `caratheodory_measure_complete`
  + internal definitions and lemmas that may be deprecated and hidden in the future:
    * `caratheodory_measurable`, notation `... .-measurable`,
    * `le_caratheodory_measurable`, `outer_measure_bigcup_lim`,
      `caratheodory_measurable_{set0,setC,setU_le,setU,bigsetU,setI,setD}`
      `disjoint_caratheodoryIU`, `caratheodory_additive`,
          `caratheodory_lim_lee`, `caratheodory_measurable_trivIset_bigcup`,
      `caratheodory_measurable_bigcup`
  + definition `measure_is_complete`
- file `csum.v`:
  + lemmas `ereal_pseries_pred0`, `ub_ereal_sup_adherent_img`
  + definition `fsets`, lemmas `fsets_set0`, `fsets_self`, `fsetsP`, `fsets_img`
  + definition `fsets_ord`, lemmas `fsets_ord_nat`, `fsets_ord_subset`
  + definition `csum`, lemmas `csum0`, `csumE`, `csum_ge0`, `csum_fset`
    `csum_image`, `ereal_pseries_csum`, `csum_bigcup`
  + notation `\csum_(i in S) a i`
- file `cardinality.v`
  + lemmas `in_inj_comp`, `enum0`, `enum_recr`, `eq_set0_nil`, `eq_set0_fset0`,
    `image_nat_maximum`, `fset_nat_maximum`
  + defintion `surjective`, lemmas `surjective_id`, `surjective_set0`,
    `surjective_image`, `surjective_image_eq0`, `surjective_comp`
  + definition `set_bijective`,
  + lemmas `inj_of_bij`, `sur_of_bij`, `set_bijective1`, `set_bijective_image`,
    `set_bijective_subset`, `set_bijective_comp`
  + definition `inverse`
  + lemmas `injective_left_inverse`, `injective_right_inverse`,
    `surjective_right_inverse`,
  + notation `` `I_n ``
  + lemmas `II0`, `II1`, `IIn_eq0`, `II_recr`
  + lemmas `set_bijective_D1`, `pigeonhole`, `Cantor_Bernstein`
  + definition `card_le`, notation `_ #<= _`
  + lemmas `card_le_surj`, `surj_card_le`, `card_lexx`, `card_le0x`,
    `card_le_trans`, `card_le0P`, `card_le_II`
  + definition `card_eq`, notation `_ #= _`
  + lemmas `card_eq_sym`, `card_eq_trans`, `card_eq00`, `card_eqP`, `card_eqTT`,
    `card_eq_II`, `card_eq_le`, `card_eq_ge`, `card_leP`
  + lemma `set_bijective_inverse`
  + definition `countable`
  + lemmas `countable0`, `countable_injective`, `countable_trans`
  + definition `set_finite`
  + lemmas `set_finiteP`, `set_finite_seq`, `set_finite_countable`, `set_finite0`
  + lemma `set_finite_bijective`
  + lemmas `subset_set_finite`, `subset_card_le`
  + lemmas `injective_set_finite`, `injective_card_le`, `set_finite_preimage`
  + lemmas `surjective_set_finite`, `surjective_card_le`
  + lemmas `set_finite_diff`, `card_le_diff`
  + lemmas `set_finite_inter_set0_union`, `set_finite_inter`
  + lemmas `ex_in_D`, definitions `min_of_D`, `min_of_D_seq`, `infsub_enum`, lemmas
    `min_of_D_seqE`, `increasing_infsub_enum`, `sorted_infsub_enum`,
   `injective_infsub_enum`, `subset_infsub_enum`, `infinite_nat_subset_countable`
  + definition `enumeration`, lemmas `enumeration_id`, `enumeration_set0`.
  + lemma `ex_enum_notin`, definitions `min_of`, `minf_of_e_seq`, `smallest_of`
  + definition `enum_wo_rep`, lemmas `enum_wo_repE`, `min_of_e_seqE`,
    `smallest_of_e_notin_enum_wo_rep`, `injective_enum_wo_rep`, `surjective_enum_wo_rep`,
    `set_bijective_enum_wo_rep`, `enumration_enum_wo_rep`, `countable_enumeration`
  + lemmas `infinite_nat`, `infinite_prod_nat`, `countable_prod_nat`,
    `countably_infinite_prod_nat`

### Changed

- in `classical_sets.v`
  + lemma `subset_bigsetU`
  + notation ``f @` A`` defined as `[set f x | x in A]` instead of using `image`
- in `ereal.v`:
  + change implicits of lemma `lee_sum_nneg_ord`
  + `ereal_sup_ninfty` and `ereal_inf_pinfty` made equivalences
  + change the notation `{ereal R}` to `\bar R` and attach it to the scope `ereal_scope`
  + argument of `%:E` in `%R` by default
  + `F` argument of `\sum` in `%E` by default
- in `topology.v`:
  + change implicits of lemma `cvg_app`
- in `normedtype.v`:
  + `coord_continuous` generalized
- in `sequences.v`:
  + change implicits of lemma `is_cvg_ereal_nneg_series`
  + statements changed from using sum of ordinals to sum of nats
    * definition `series`
    * lemmas `ereal_nondecreasing_series`, `ereal_nneg_series_lim_ge`
    * lemmas `is_cvg_ereal_nneg_series_cond`, `is_cvg_ereal_nneg_series`
    * lemmas `ereal_nneg_series_lim_ge0`, `ereal_nneg_series_pinfty`

### Renamed

- in `ereal.v`:
  + `er` -> `extended`
  + `ERFin` -> `EFin`
  + `ERPInf` -> `EPInf`
  + `ERNInf` -> `ENInf`
  + `real_of_er` -> `real_of_extended`
  + `real_of_erD` -> `real_of_extendedD`
  + `ERFin_real_of_er` -> `EFin_real_of_extended`
  + `real_of_er_expand` -> `real_of_extended_expand`
  + `NERFin` -> `NEFin`
  + `addERFin` -> `addEFin`
  + `sumERFin`-> `sumEFin`
  + `subERFin` -> `subEFin`
- in `reals.v`:
  + `ler_ceil` -> `ceil_ge`
  + `Rceil_le` -> `le_Rceil`
  + `le_Rceil` -> `Rceil_ge`
  + `ge_Rfloor` -> `Rfloor_le`
  + `ler_floor` -> `floor_le`
  + `Rfloor_le` -> `le_Rfloor`
- in `topology.v`:
  + lemmas `onT_can` -> `onS_can`,
    `onT_can_in` -> `onS_can_in`,
    `in_onT_can` -> ``in_onS_can`
    (now in MathComp)
- in `sequences,v`:
  + `is_cvg_ereal_nneg_series_cond`
- in `forms.v`:
  + `symmetric` -> `symmetric_form`

### Removed

- in `classical_sets.v`
  + lemmas `eq_set_inl`, `set_in_in`
  + definition `image`
- from `topology.v`:
  + lemmas `homoRL_in`, `homoLR_in`, `homo_mono_in`, `monoLR_in`,
    `monoRL_in`, `can_mono_in`, `onW_can`, `onW_can_in`, `in_onW_can`,
    `onT_can`, `onT_can_in`, `in_onT_can` (now in MathComp)
- in `forms.v`:
  + lemma `mxdirect_delta`, `row_mx_eq0`, `col_mx_eq0`, `map_mx_comp`

## [0.3.7] - 2021-04-01

### Added

- in `topology.v`:
  + global instance `ball_filter`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pointedType`, `filteredType`, `topologicalType`,
      `uniformType`, `pseudoMetricType`
  + module `numFieldTopology` with an `Exports` submodule
    * many canonicals and coercions
  + global instance `Proper_nbhs'_regular_numFieldType`
  + definition `dense` and lemma `denseNE`
- in `normedtype.v`:
  + definitions `ball_`, `pointed_of_zmodule`, `filtered_of_normedZmod`
  + lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`
  + definition `pseudoMetric_of_normedDomain`
  + lemma `nbhs_ball_normE`
  + global instances `Proper_nbhs'_numFieldType`, `Proper_nbhs'_realType`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pseudoMetricNormedZmodType`, `normedModType`.
  + module `numFieldNormedType` with an `Exports` submodule
    * many canonicals and coercions
    * exports `Export numFieldTopology.Exports`
  + canonical `R_regular_completeType`, `R_regular_CompleteNormedModule`
- in `reals.v`:
  + lemmas `Rfloor_lt0`, `floor_lt0`, `ler_floor`, `ceil_gt0`, `ler_ceil`
  + lemmas `has_sup1`, `has_inf1`
- in `ereal.v`:
  + lemmas `ereal_ballN`, `le_ereal_ball`, `ereal_ball_ninfty_oversize`,
    `contract_ereal_ball_pinfty`, `expand_ereal_ball_pinfty`,
    `contract_ereal_ball_fin_le`, `contract_ereal_ball_fin_lt`,
    `expand_ereal_ball_fin_lt`, `ball_ereal_ball_fin_lt`, `ball_ereal_ball_fin_le`,
    `sumERFin`, `ereal_inf1`, `eqe_oppP`, `eqe_oppLRP`, `oppe_subset`,
    `ereal_inf_pinfty`
  + definition `er_map`
  + definition `er_map`
  + lemmas `adde_undefC`, `real_of_erD`, `fin_num_add_undef`, `addeK`,
    `subeK`, `subee`, `sube_le0`, `lee_sub`
  + lemmas `addeACA`, `muleC`, `mule1`, `mul1e`, `abseN`
  + enable notation `x \is a fin_num`
    * definition `fin_num`, fact `fin_num_key`, lemmas `fin_numE`, `fin_numP`
- in `classical_sets.v`:
  + notation `[disjoint ... & ..]`
  + lemmas `mkset_nil`, `bigcup_mkset`, `bigcup_nonempty`, `bigcup0`, `bigcup0P`,
    `subset_bigcup_r`, `eqbigcup_r`, `eq_set_inl`, `set_in_in`
- in `nngnum.v`:
  + instance `invr_nngnum`
- in `posnum.v`:
  + instance `posnum_nngnum`

## Changed

- in `ereal.v`:
  + generalize lemma `lee_sum_nneg_subfset`
  + lemmas `nbhs_oo_up_e1`, `nbhs_oo_down_e1`, `nbhs_oo_up_1e`, `nbhs_oo_down_1e`
    `nbhs_fin_out_above`, `nbhs_fin_out_below`, `nbhs_fin_out_above_below`
    `nbhs_fin_inbound`
- in `sequences.v`:
  + generalize lemmas `ereal_nondecreasing_series`, `is_cvg_ereal_nneg_series`,
    `ereal_nneg_series_lim_ge0`, `ereal_nneg_series_pinfty`
- in `measure.v`:
  + generalize lemma `bigUB_of`
  + generalize theorem `Boole_inequality`
- in `classical_sets.v`:
  + change the order of arguments of `subset_trans`

- canonicals and coercions have been changed so that there is not need
  anymore for explicit types casts to `R^o`, `[filteredType R^o of R^o]`,
  `[filteredType R^o * R^o of R^o * R^o]`, `[lmodType R of R^o]`,
  `[normedModType R of R^o]`,`[topologicalType of R^o]`, `[pseudoMetricType R of R^o]`
- `sequences.v` now imports `numFieldNormedType.Exports`
- `topology.v` now imports `reals`
- `normedtype.v` now imports `vector`, `fieldext`, `falgebra`,
  `numFieldTopology.Exports`
- `derive.v` now imports `numFieldNormedType.Exports`

### Renamed

- in `ereal.v`:
  + `is_realN` -> `fin_numN`
  + `is_realD` -> `fin_numD`
  + `ereal_sup_set0` -> `ereal_sup0`
  + `ereal_sup_set1` -> `ereal_sup1`
  + `ereal_inf_set0` -> `ereal_inf0`

### Removed

- in `topology.v`:
  + section `numFieldType_canonical`
- in `normedtype.v`:
  + lemma `R_ball`
  + definition `numFieldType_pseudoMetricNormedZmodMixin`
  + canonical `numFieldType_pseudoMetricNormedZmodType`
  + global instance `Proper_nbhs'_realType`
  + lemma `R_normZ`
  + definition `numFieldType_NormedModMixin`
  + canonical `numFieldType_normedModType`
- in `ereal.v`:
  + definition `is_real`

## [0.3.6] - 2021-03-04

### Added

- in `boolp.v`:
  + lemmas `iff_notr`, `iff_not2`
- in `classical_sets.v`:
  + lemmas `subset_has_lbound`, `subset_has_ubound`
  + lemma `mksetE`
  + definitions `cover`, `partition`, `pblock_index`, `pblock`
  + lemmas `trivIsetP`, `trivIset_sets`, `trivIset_restr`, `perm_eq_trivIset`
  + lemma `fdisjoint_cset`
  + lemmas `setDT`, `set0D`, `setD0`
  + lemmas `setC_bigcup`, `setC_bigcap`
- in `reals.v`:
  + lemmas `sup_setU`, `inf_setU`
  + lemmas `RtointN`, `floor_le0`
  + definition `Rceil`, lemmas `isint_Rceil`, `Rceil0`, `le_Rceil`, `Rceil_le`, `Rceil_ge0`
  + definition `ceil`, lemmas `RceilE`, `ceil_ge0`, `ceil_le0`
- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`, `esum_pinfty`
- in `normedtype.v`:
  + lemmas `ereal_nbhs'_le`, `ereal_nbhs'_le_finite`
  + lemmas `ball_open`
  + definition `closed_ball_`, lemmas `closed_closed_ball_`
  + definition `closed_ball`, lemmas `closed_ballxx`, `closed_ballE`,
    `closed_ball_closed`, `closed_ball_subset`, `nbhs_closedballP`, `subset_closed_ball`
  + lemmas `nbhs0_lt`, `nbhs'0_lt`, `interior_closed_ballE`, open_nbhs_closed_ball`
  + section "LinearContinuousBounded"
    * lemmas `linear_boundedP`, `linear_continuous0`, `linear_bounded0`,
      `continuousfor0_continuous`, `linear_bounded_continuous`, `bounded_funP`
- in `measure.v`:
  + definition `sigma_finite`

### Changed

- in `classical_sets.v`:
  + generalization and change of `trivIset` (and thus lemmas `trivIset_bigUI` and `trivIset_setI`)
  + `bigcup_distrr`, `bigcup_distrl` generalized
- header in `normedtype.v`, precisions on `bounded_fun`
- in `reals.v`:
  + `floor_ge0` generalized and renamed to `floorR_ge_int`
- in `ereal.v`, `ereal_scope` notation scope:
  + `x <= y` notation changed to `lee (x : er _) (y : er _)` and
    `only printing` notation `x <= y` for `lee x y`
  + same change for `<`
  + change extended to notations `_ <= _ <= _`, `_ < _ <= _`, `_ <= _ < _`, `_ < _ < _`

### Renamed

- in `reals.v`:
  + `floor` -> `Rfloor`
  + `isint_floor` -> `isint_Rfloor`
  + `floorE` -> `RfloorE`
  + `mem_rg1_floor` -> `mem_rg1_Rfloor`
  + `floor_ler` -> `Rfloor_ler`
  + `floorS_gtr` -> `RfloorS_gtr`
  + `floor_natz` -> `Rfloor_natz`
  + `Rfloor` -> `Rfloor0`
  + `floor1` -> `Rfloor1`
  + `ler_floor` -> `ler_Rfloor`
  + `floor_le0` -> `Rfloor_le0`
  + `ifloor` -> `floor`
  + `ifloor_ge0` -> `floor_ge0`
- in `topology.v`:
  + `ball_ler` -> `le_ball`
- in `normedtype.v`, `bounded_on` -> `bounded_near`
- in `measure.v`:
  + `AdditiveMeasure.Measure` -> `AdditiveMeasure.Axioms`
  + `OuterMeasure.OuterMeasure` -> `OuterMeasure.Axioms`

### Removed
- in `topology.v`:
  + `ball_le`
- in `classical_sets.v`:
  + lemma `bigcapCU`
- in `sequences.v`:
  + lemmas `ler_sum_nat`, `sumr_const_nat`

## [0.3.5] - 2020-12-21

### Added

- in `classical_sets.v`:
  + lemmas `predeqP`, `seteqP`

### Changed

- Requires:
  + MathComp >= 1.12
- in `boolp.v`:
  + lemmas `contra_not`, `contra_notT`, `contra_notN`, `contra_not_neq`, `contraPnot`
    are now provided by MathComp 1.12
- in `normedtype.v`:
  + lemmas `ltr_distW`, `ler_distW` are now provided by MathComp 1.12 as lemmas
    `ltr_distlC_subl` and `ler_distl_subl`
  + lemmas `maxr_real` and `bigmaxr_real` are now provided by MathComp 1.12 as
    lemmas `max_real` and `bigmax_real`
  + definitions `isBOpen` and `isBClosed` are replaced by the definition `bound_side`
  + definition `Rhull` now uses `BSide` instead of `BOpen_if`

### Removed

- Drop support for MathComp 1.11
- in `topology.v`:
  + `Typeclasses Opaque fmap.`

## [0.3.4] - 2020-12-12

### Added

- in `classical_sets.v`:
  + lemma `bigcup_distrl`
  + definition `trivIset`
  + lemmas `trivIset_bigUI`, `trivIset_setI`
- in `ereal.v`:
  + definition `mule` and its notation `*` (scope `ereal_scope`)
  + definition `abse` and its notation `` `| | `` (scope `ereal_scope`)
- in `normedtype.v`:
  + lemmas `closure_sup`, `near_infty_natSinv_lt`, `limit_pointP`
  + lemmas `closure_gt`, `closure_lt`
  + definition `is_interval`, `is_intervalPle`, `interval_is_interval`
  + lemma `connected_intervalP`
  + lemmas `interval_open` and `interval_closed`
  + lemmas `inf_lb_strict`, `sup_ub_strict`, `interval_unbounded_setT`,
    `right_bounded_interior`, `interval_left_unbounded_interior`, `left_bounded_interior`,
    `interval_right_unbounded_interior`, `interval_bounded_interior`
  + definition `Rhull`
  + lemma `sub_Rhull`, `is_intervalP`
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`
  + definitions `isSemiRingOfSets`, `SemiRingOfSets`, notation `semiRingOfSetsType`
  + definitions `RingOfSets_from_semiRingOfSets`, `RingOfSets`, notation `ringOfSetsType`
  + factory: `isRingOfSets`
  + definitions `Measurable_from_ringOfSets`, `Measurable`
  + lemma `semiRingOfSets_measurable{I,D}`
  + definition `diff_fsets`, lemmas `semiRingOfSets_diff_fsetsE`, `semiRingOfSets_diff_fsets_disjoint`
  + definitions `isMeasurable`
  + factory: `isMeasurable`
  + lemma `bigsetU_measurable`, `measurable_bigcap`
  + definitions `semi_additive2`, `semi_additive`, `semi_sigma_additive`
  + lemmas `semi_additive2P`, `semi_additiveE`, `semi_additive2E`,
    `semi_sigma_additive_is_additive`, `semi_sigma_additiveE`
  + `Module AdditiveMeasure`
     * notations `additive_measure`, `{additive_measure set T -> {ereal R}}`
  + lemmas `measure_semi_additive2`, `measure_semi_additive`, `measure_semi_sigma_additive`
  + lemma `semi_sigma_additive_is_additive`, canonical/coercion `measure_additive_measure`
  + lemma `sigma_additive_is_additive`
  + notations `ringOfSetsType`, `outer_measure`
  + definition `negligible` and its notation `.-negligible`
  + lemmas `negligibleP`, `negligible_set0`
  + definition `almost_everywhere` and its notation `{ae mu, P}`
  + lemma `satisfied_almost_everywhere`
  + definition `sigma_subadditive`
  + `Module OuterMeasure`
    * notation `outer_measure`, `{outer_measure set T -> {ereal R}}`
  + lemmas `outer_measure0`, `outer_measure_ge0`, `le_outer_measure`,
    `outer_measure_sigma_subadditive`, `le_outer_measureIC`
- in `boolp.v`:
  + lemmas `and3_asboolP`, `or3_asboolP`, `not_and3P`
- in `classical_sets.v`:
  + lemma `bigcup_sup`
- in `topology.v`:
  + lemmas `closure0`, `separatedC`, `separated_disjoint`, `connectedP`, `connected_subset`,
    `bigcup_connected`
  + definition `connected_component`
  + lemma `component_connected`

### Changed

- in `ereal.v`:
  + notation `x >= y` defined as `y <= x` (only parsing) instead of `gee`
  + notation `x > y` defined as `y < x` (only parsing) instead of `gte`
  + definition `mkset`
  + lemma `eq_set`
- in `classical_sets.v`:
  + notation `[set x : T | P]` now use definition `mkset`
- in `reals.v`:
  + lemmas generalized from `realType` to `numDomainType`:
    `setNK`, `memNE`, `lb_ubN`, `ub_lbN`, `nonemptyN`, `has_lb_ubN `
  + lemmas generalized from `realType` to `realDomainType`:
    `has_ubPn`, `has_lbPn`

## Renamed

- in `classical_sets.v`:
  + `subset_empty` -> `subset_nonempty`
- in `measure.v`:
  + `sigma_additive_implies_additive` -> `sigma_additive_is_additive`
- in `topology.v`:
  + `nbhs_of` -> `locally_of`
- in `topology.v`:
  + `connect0` -> `connected0`

## [0.3.3] - 2020-11-11

### Added

- in `boolp.v`:
  + lemma `not_andP`
  + lemma `not_exists2P`
- in `classical_sets.v`:
  + lemmas `setIIl`, `setIIr`, `setCS`, `setSD`, `setDS`, `setDSS`, `setCI`,
    `setDUr`, `setDUl`, `setIDA`, `setDD`
  + definition `dep_arrow_choiceType`
  + lemma `bigcup_set0`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`, `subsetEset`, `subEset`, `complEset`, `botEset`, `topEset`, `meetEset`, `joinEset`, `subsetPset`, `properPset`
  + Canonical `porderType`, `latticeType`, `distrLatticeType`, `blatticeType`, `tblatticeType`, `bDistrLatticeType`, `tbDistrLatticeType`, `cbDistrLatticeType`, `ctbDistrLatticeType`
  + lemmas `set0M`, `setM0`, `image_set0_set0`, `subset_set1`, `preimage_set0`
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
  + new lemmas: `lb_set1`, `ub_lb_set1`, `ub_lb_refl`, `lb_ub_lb`
  + new definitions and lemmas: `infimums`, `infimum`, `infimums_set1`, `is_subset1_infimum`
  + new lemmas: `ge_supremum_Nmem`, `le_infimum_Nmem`, `nat_supremums_neq0`
  + lemmas `setUCl`, `setDv`
  + lemmas `image_preimage_subset`, `image_subset`, `preimage_subset`
  + definition `proper` and its notation `<`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`, `subsetEset`, `subEset`, `complEset`, `botEset`, `topEset`, `meetEset`, `joinEset`, `properEneq`
  + Canonical `porderType`, `latticeType`, `distrLatticeType`, `blatticeType`, `tblatticeType`, `bDistrLatticeType`, `tbDistrLatticeType`, `cbDistrLatticeType`, `ctbDistrLatticeType` on classical `set`.
- file `nngnum.v`
- in `topology.v`:
  + definition `meets` and its notation `#`
  + lemmas `meetsC`, `meets_openr`, `meets_openl`, `meets_globallyl`,
    `meets_globallyr `, `meetsxx` and `proper_meetsxx`.
  + definition `limit_point`
  + lemmas `subset_limit_point`, `closure_limit_point`,
    `closure_subset`, `closureE`, `closureC`, `closure_id`
  + lemmas `cluster_nbhs`, `clusterEonbhs`, `closureEcluster`
  + definition `separated`
  + lemmas `connected0`, `connectedPn`, `connected_continuous_connected`
  + lemmas `closureEnbhs`, `closureEonbhs`, `limit_pointEnbhs`,
    `limit_pointEonbhs`, `closeEnbhs`, `closeEonbhs`.
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`
  + lemmas `gee0P`, `sume_ge0`, `lee_sum_nneg`, `lee_sum_nneg_ord`, `lee_sum_nneg_subset`, `lee_sum_nneg_subfset`
  + lemma `lee_addr`
  + lemma `lee_adde`
  + lemma `oppe_continuous`
  + lemmas `ereal_nbhs_pinfty_ge`, `ereal_nbhs_ninfty_le`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`, `geometric_invn`
  + lemmas `increasing_series`, `cvg_shiftS`, `mulrn_arithmetic`,
    `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`,
    `is_cvg_geometric_series`.
  + lemmas `ereal_cvgN`, `ereal_cvg_ge0`, `ereal_lim_ge`, `ereal_lim_le`
  + lemma `ereal_cvg_real`
  + lemmas `is_cvg_ereal_nneg_series_cond`, `is_cvg_ereal_nneg_series`, `ereal_nneg_series_lim_ge0`,
    `ereal_nneg_series_pinfty`
  + lemmas `ereal_cvgPpinfty`, `ereal_cvgPninfty`, `lee_lim`
  + lemma `ereal_cvgD`
    * with intermediate lemmas `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`, `ereal_cvgD_pinfty_pinfty`,
      `ereal_cvgD_ninfty_ninfty`
  + lemma `ereal_limD`
- in `normedtype.v`:
  + lemma `closed_ereal_le_ereal`
  + lemma `closed_ereal_ge_ereal`
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`

### Changed

- in `classical_sets.v`:
  + the index in `bigcup_set1` generalized from `nat` to some `Type`
  + lemma `bigcapCU` generalized
  + lemmas `preimage_setU` and `preimage_setI` are about the `setU` and `setI` (instead of `bigcup` and `bigcap`)
  + `eqEsubset` changed from an implication to an equality
- lemma `asboolb` moved from `discrete.v` to `boolp.v`
- lemma `exists2NP` moved from `discrete.v` to `boolp.v`
- lemma `neg_or` moved from `discrete.v` to `boolp.v` and renamed to `not_orP`
- definitions `dep_arrow_choiceClass` and `dep_arrow_pointedType`
  slightly generalized and moved from `topology.v` to
  `classical_sets.v`
- the types of the topological notions for `numFieldType` have been moved from `normedtype.v` to `topology.v`
- the topology of extended real numbers has been moved from `normedtype.v` to `ereal.v` (including the notions of filters)
- `numdFieldType_lalgType` in `normedtype.v` renamed to `numFieldType_lalgType` in `topology.v`
- in `ereal.v`:
  + the first argument of `real_of_er` is now maximal implicit
  + the first argument of `is_real` is now maximal implicit
  + generalization of `lee_sum`
- in `boolp.v`:
  + rename `exists2NP` to `forall2NP` and make it bidirectionnal
- moved the definition of `{nngnum _}` and the related bigmax theory to the new `nngnum.v` file

### Renamed

- in `classical_sets.v`:
  + `setIDl` -> `setIUl`
  + `setUDl` -> `setUIl`
  + `setUDr` -> `setUIr`
  + `setIDr` -> `setIUl`
  + `setCE` -> `setTD`
  + `preimage_setU` -> `preimage_bigcup`, `preimage_setI` -> `preimage_bigcap`
- in `boolp.v`:
  + `contrap` -> `contra_not`
  + `contrapL` -> `contraPnot`
  + `contrapR` -> `contra_notP`
  + `contrapLR` -> `contraPP`

### Removed

- in `boolp.v`:
  + `contrapNN`, `contrapTN`, `contrapNT`, `contrapTT`
  + `eqNN`
- in `normedtype.v`:
  + `forallN`
  + `eqNNP`
  + `existsN`
- in `discrete.v`:
  + `existsP`
  + `existsNP`
- in `topology.v`:
  + `close_to`
  + `close_cluster`, which is subsumed by `closeEnbhs`

## [0.3.2] - 2020-08-11

### Added

- in `boolp.v`, new lemma `andC`
- in `topology.v`:
  + new lemma `open_nbhsE`
  + `uniformType` a structure for uniform spaces based on entourages
    (`entourage`)
  + `uniformType` structure on products, matrices, function spaces
  + definitions `nbhs_`, `topologyOfEntourageMixin`, `split_ent`, `nbhsP`,
    `entourage_set`, `entourage_`, `uniformityOfBallMixin`, `nbhs_ball`
  + lemmas `nbhs_E`, `nbhs_entourageE`, `filter_from_entourageE`,
    `entourage_refl`, `entourage_filter`, `entourageT`, `entourage_inv`,
    `entourage_split_ex`, `split_entP`, `entourage_split_ent`,
    `subset_split_ent`, `entourage_split`, `nbhs_entourage`, `cvg_entourageP`,
    `cvg_entourage`, `cvg_app_entourageP`, `cvg_mx_entourageP`,
    `cvg_fct_entourageP`, `entourage_E`, `entourage_ballE`,
    `entourage_from_ballE`, `entourage_ball`, `entourage_proper_filter`,
    `open_nbhs_entourage`, `entourage_close`
  + `completePseudoMetricType` structure
  + `completePseudoMetricType` structure on matrices and function spaces
- in `classical_sets.v`:
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`, `adde_undef`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`, `addeAC`, `addeCA`
- in `normedtype.v`:
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`
  + lemmas `telescopeK`, `seriesK`, `increasing_series`, `cvg_shiftS`,
     `mulrn_arithmetic`, `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`, `is_cvg_geometric_series`.

### Changed

- moved from `normedtype.v` to `boolp.v` and renamed:
  + `forallN` -> `forallNE`
  + `existsN` -> `existsNE`
- `topology.v`:
  + `unif_continuous` uses `entourage`
  + `pseudoMetricType` inherits from `uniformType`
  + `generic_source_filter` and `set_filter_source` use entourages
  + `cauchy` is based on entourages and its former version is renamed
    `cauchy_ball`
  + `completeType` inherits from `uniformType` and not from `pseudoMetricType`
- moved from `posnum.v` to `Rbar.v`: notation `posreal`
- moved from `normedtype.v` to `Rstruct.v`:
  + definitions `R_pointedType`, `R_filteredType`, `R_topologicalType`,
    `R_uniformType`, `R_pseudoMetricType`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`, `continuity_ptE`,
    `continuity_pt_cvg'`, `continuity_pt_nbhs'`, `nbhs_pt_comp`
  + lemmas `close_trans`, `close_cvgxx`, `cvg_closeP` and `close_cluster` are
    valid for a `uniformType`
  + moved `continuous_withinNx` from `normedType.v` to `topology.v` and
    generalised it to `uniformType`
- moved from `measure.v` to `sequences.v`
  + `ereal_nondecreasing_series`
  + `ereal_nneg_series_lim_ge` (renamed from `series_nneg`)

### Renamed

- in `classical_sets.v`,
  + `ub` and `lb` are renamed to `ubound` and `lbound`
  + new lemmas:
    * `setUCr`, `setCE`, `bigcup_set1`, `bigcapCU`, `subset_bigsetU`
- in `boolp.v`,
  + `existsPN` -> `not_existsP`
  + `forallPN` -> `not_forallP`
  + `Nimply` -> `not_implyP`
- in `classical_sets.v`, `ub` and `lb` are renamed to `ubound` and `lbound`
- in `ereal.v`:
  + `eadd` -> `adde`, `eopp` -> `oppe`
- in `topology.v`:
  + `locally` -> `nbhs`
  + `locally_filterE` -> `nbhs_filterE`
  + `locally_nearE` -> `nbhs_nearE`
  + `Module Export LocallyFilter` -> `Module Export NbhsFilter`
  + `locally_simpl` -> `nbhs_simpl`
    * three occurrences
  + `near_locally` -> `near_nbhs`
  + `Module Export NearLocally` -> `Module Export NearNbhs`
  + `locally_filter_onE` -> `nbhs_filter_onE`
  + `filter_locallyT` -> `filter_nbhsT`
  + `Global Instance locally_filter` -> `Global Instance nbhs_filter`
  + `Canonical locally_filter_on` -> `Canonical nbhs_filter_on`
  + `neigh` -> `open_nbhs`
  + `locallyE` -> `nbhsE`
  + `locally_singleton` -> `nbhs_singleton`
  + `locally_interior` -> `nbhs_interior`
  + `neighT` -> `open_nbhsT`
  + `neighI` -> `open_nbhsI`
  + `neigh_locally` -> `open_nbhs_nbhs`
  + `within_locallyW` -> `within_nbhsW`
  + `prod_loc_filter` -> `prod_nbhs_filter`
  + `prod_loc_singleton` -> `prod_nbhs_singleton`
  + `prod_loc_loc` -> `prod_nbhs_nbhs`
  + `mx_loc_filter` -> `mx_nbhs_filter`
  + `mx_loc_singleton` -> `mx_nbhs_singleton`
  + `mx_loc_loc` -> `mx_nbhs_nbhs`
  + `locally'` -> `nbhs'`
  + `locallyE'` -> `nbhsE'`
  + `Global Instance locally'_filter` -> `Global Instance nbhs'_filter`
  + `Canonical locally'_filter_on` -> `Canonical nbhs'_filter_on`
  + `locally_locally'` -> `nbhs_nbhs'`
  + `Global Instance within_locally_proper` -> `Global Instance within_nbhs_proper`
  + `locallyP` -> `nbhs_ballP`
  + `locally_ball` -> `nbhsx_ballx`
  + `neigh_ball` -> `open_nbhs_ball`
  + `mx_locally` -> `mx_nbhs`
  + `prod_locally` -> `prod_nbhs`
  + `Filtered.locally_op` -> `Filtered.nbhs_op`
  + `locally_of` -> `nbhs_of`
  + `open_of_locally` -> `open_of_nhbs`
  + `locally_of_open` -> `nbhs_of_open`
  + `locally_` -> `nbhs_ball`
  + lemma `locally_ballE` -> `nbhs_ballE`
  + `locallyW` -> `nearW`
  + `nearW` -> `near_skip_subproof`
  + `locally_infty_gt` -> `nbhs_infty_gt`
  + `locally_infty_ge` -> `nbhs_infty_ge`
  + `cauchy_entouragesP` -> `cauchy_ballP`
- in `normedtype.v`:
  + `locallyN` -> `nbhsN`
  + `locallyC` -> `nbhsC`
  + `locallyC_ball` -> `nbhsC_ball`
  + `locally_ex` -> `nbhs_ex`
  + `Global Instance Proper_locally'_numFieldType` -> `Global Instance Proper_nbhs'_numFieldType`
  + `Global Instance Proper_locally'_realType` -> `Global Instance Proper_nbhs'_realType`
  + `ereal_locally'` -> `ereal_nbhs'`
  + `ereal_locally` -> `ereal_nbhs`
  + `Global Instance ereal_locally'_filter` -> `Global Instance ereal_nbhs'_filter`
  + `Global Instance ereal_locally_filter` -> `Global Instance ereal_nbhs_filter`
  + `ereal_loc_singleton` -> `ereal_nbhs_singleton`
  + `ereal_loc_loc` -> `ereal_nbhs_nbhs`
  + `locallyNe` -> `nbhsNe`
  + `locallyNKe` -> `nbhsNKe`
  + `locally_oo_up_e1` -> `nbhs_oo_up_e1`
  + `locally_oo_down_e1` -> `nbhs_oo_down_e1`
  + `locally_oo_up_1e` -> `nbhs_oo_up_1e`
  + `locally_oo_down_1e` -> `nbhs_oo_down_1e`
  + `locally_fin_out_above` -> `nbhs_fin_out_above`
  + `locally_fin_out_below` -> `nbhs_fin_out_below`
  + `locally_fin_out_above_below` -> `nbhs_fin_out_above_below`
  + `locally_fin_inbound` -> `nbhs_fin_inbound`
  + `ereal_locallyE` -> `ereal_nbhsE`
  + `locally_le_locally_norm` -> `nbhs_le_locally_norm`
  + `locally_norm_le_locally` -> `locally_norm_le_nbhs`
  + `locally_locally_norm` -> `nbhs_locally_norm`
  + `filter_from_norm_locally` -> `filter_from_norm_nbhs`
  + `locally_ball_norm` -> `nbhs_ball_norm`
  + `locally_simpl` -> `nbhs_simpl`
  + `Global Instance filter_locally` -> `Global Instance filter_locally`
  + `locally_interval` -> `nbhs_interval`
  + `ereal_locally'_le` -> `ereal_nbhs'_le`
  + `ereal_locally'_le_finite` -> `ereal_nbhs'_le_finite`
  + `locally_image_ERFin` -> `nbhs_image_ERFin`
  + `locally_open_ereal_lt` -> `nbhs_open_ereal_lt`
  + `locally_open_ereal_gt` -> `nbhs_open_ereal_gt`
  + `locally_open_ereal_pinfty` -> `nbhs_open_ereal_pinfty`
  + `locally_open_ereal_ninfty` -> `nbhs_open_ereal_ninfty`
  + `continuity_pt_locally` -> `continuity_pt_nbhs`
  + `continuity_pt_locally'` -> `continuity_pt_nbhs'`
  + `nbhs_le_locally_norm` -> `nbhs_le_nbhs_norm`
  + `locally_norm_le_nbhs` -> `nbhs_norm_le_nbhs`
  + `nbhs_locally_norm` -> `nbhs_nbhs_norm`
  + `locally_normP` -> `nbhs_normP`
  + `locally_normE` -> `nbhs_normE`
  + `near_locally_norm` -> `near_nbhs_norm`
  + lemma `locally_norm_ball_norm` -> `nbhs_norm_ball_norm`
  + `locally_norm_ball` -> `nbhs_norm_ball`
  + `pinfty_locally` -> `pinfty_nbhs`
  + `ninfty_locally` -> `ninfty_nbhs`
  + lemma `locally_pinfty_gt` -> `nbhs_pinfty_gt`
  + lemma `locally_pinfty_ge` -> `nbhs_pinfty_ge`
  + lemma `locally_pinfty_gt_real` -> `nbhs_pinfty_gt_real`
  + lemma `locally_pinfty_ge_real` -> `nbhs_pinfty_ge_real`
  + `locally_minfty_lt` -> `nbhs_minfty_lt`
  + `locally_minfty_le` -> `nbhs_minfty_le`
  + `locally_minfty_lt_real` -> `nbhs_minfty_lt_real`
  + `locally_minfty_le_real` -> `nbhs_minfty_le_real`
  + `lt_ereal_locally` -> `lt_ereal_nbhs`
  + `locally_pt_comp` -> `nbhs_pt_comp`
- in `derive.v`:
  + `derivable_locally` -> `derivable_nbhs`
  + `derivable_locallyP` -> `derivable_nbhsP`
  + `derivable_locallyx` -> `derivable_nbhsx`
  + `derivable_locallyxP` -> `derivable_nbhsxP`
- in `sequences.v`,
  + `cvg_comp_subn` -> `cvg_centern`,
  + `cvg_comp_addn` -> `cvg_shiftn`,
  + `telescoping` -> `telescope`
  + `sderiv1_series` -> `seriesSB`
  + `telescopingS0` -> `eq_sum_telescope`

### Removed

- in `topology.v`:
  + definitions `entourages`, `topologyOfBallMixin`, `ball_set`
  + lemmas `locally_E`, `entourages_filter`, `cvg_cauchy_ex`

## [0.3.1] - 2020-06-11

### Added

- in `boolp.v`, lemmas for classical reasoning `existsNP`, `existsPN`,
  `forallNP`, `forallPN`, `Nimply`, `orC`.
- in `classical_sets.v`, definitions for supremums: `ul`, `lb`,
  `supremum`
- in `ereal.v`:
  + technical lemmas `lee_ninfty_eq`, `lee_pinfty_eq`, `lte_subl_addr`, `eqe_oppLR`
  + lemmas about supremum: `ereal_supremums_neq0`
  + definitions:
    * `ereal_sup`, `ereal_inf`
  + lemmas about `ereal_sup`:
    * `ereal_sup_ub`, `ub_ereal_sup`, `ub_ereal_sup_adherent`
- in `normedtype.v`:
  + function `contract` (bijection from `{ereal R}` to `R`)
  + function `expand` (that cancels `contract`)
  + `ereal_pseudoMetricType R`

### Changed

- in `reals.v`, `pred` replaced by `set` from `classical_sets.v`
  + change propagated in many files

## [0.3.0] - 2020-05-26

This release is compatible with MathComp version 1.11+beta1.

The biggest change of this release is compatibility with MathComp
1.11+beta1.  The latter introduces in particular ordered types.
All norms and absolute values have been unified, both in their denotation `|_| and in their theory.

### Added

- `sequences.v`: Main theorems about sequences and series, and examples
  + Definitions:
    * `[sequence E]_n` is a special notation for `fun n => E`
    * `series u_` is the sequence of partial sums
    * `[normed S]` is the series of absolute values, if S is a series
    * `harmonic` is the name of a sequence,
       apply `series` to them to get the series.
  + Theorems:
    * lots of helper lemmas to prove convergence of sequences
    * convergence of harmonic sequence
    * convergence of a series implies convergence of a sequence
    * absolute convergence implies convergence of series
- in `ereal.v`: lemmas about extended reals' arithmetic
- in `normedtype.v`: Definitions and lemmas about generic domination,
  boundedness, and lipschitz
  + See header for the notations and their localization
  + Added a bunch of combinators to extract existential witnesses
  + Added `filter_forall` (commutation between a filter and finite forall)
- about extended reals:
  + equip extended reals with a structure of topological space
  + show that extended reals are hausdorff
- in `topology.v`, predicate `close`
- lemmas about bigmaxr and argmaxr
  + `\big[max/x]_P F = F [arg max_P F]`
  + similar lemma for `bigmin`
- lemmas for `within`
- add `setICl` (intersection of set with its complement)
- `prodnormedzmodule.v`
  + `ProdNormedZmodule` transfered from MathComp
  + `nonneg` type for non-negative numbers
- `bigmaxr`/`bigminr` library
- Lemmas `interiorI`, `setCU` (complement of union is intersection of complements),
  `setICl`, `nonsubset`, `setC0`, `setCK`, `setCT`, `preimage_setI/U`, lemmas about `image`

### Changed

- in `Rstruct.v`, `bigmaxr` is now defined using `bigop`
- `inE` now supports `in_setE` and `in_fsetE`
- fix the definition of `le_ereal`, `lt_ereal`
- various generalizations to better use the hierarchy of `ssrnum` (`numDomainType`,
  `numFieldType`, `realDomainType`, etc. when possible) in `topology.v`,
  `normedtype.v`, `derive.v`, etc.

### Renamed

- renaming `flim` to `cvg`
  + `cvg` corresponds to `_ --> _`
  + `lim` corresponds to `lim _`
  + `continuous`  corresponds to continuity
  + some suffixes `_opp`, `_add` ... renamed to `N`, `D`, ...
- big refactoring about naming conventions
  + complete the theory of `cvg_`, `is_cvg_` and `lim_` in normedtype.v
    with consistent naming schemes
  + fixed differential of `inv` which was defined on `1 / x` instead of `x^-1`
  + two versions of lemmas on inverse exist
    * one in realType (`Rinv_` lemmas), for which we have differential
    * a general one `numFieldType`  (`inv_` lemmas in normedtype.v, no differential so far, just continuity)
  + renamed `cvg_norm` to `cvg_dist` to reuse the name `cvg_norm` for
    convergence under the norm
- `Uniform` renamed to `PseudoMetric`
- rename `is_prop` to `is_subset1`

### Removed

- `sub_trans` (replaced by MathComp's `subrKA`)
- `derive.v` does not require `Reals` anymore
- `Rbar.v` is almost not used anymore

### Infrastructure

- NIX support
  + see `config.nix`, `default.nix`
  + for the CI also

### Misc
