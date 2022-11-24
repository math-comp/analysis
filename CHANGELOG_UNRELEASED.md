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
  + lemma `image2_subset`
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
    `cvgr_norm_geNy`, `fcvgr2dist_ltP`, `cvgr2dist_ltP`, `cvgr2dist_lt`,
    `cvgNP`, `norm_cvg0P`, `cvgVP`, `is_cvgVE`, `cvgr_to_ge`, `cvgr_to_le`,
    `nbhs_EFin`, `nbhs_ereal_pinfty`, `nbhs_ereal_ninfty`, `fine_fcvg`,
    `fcvg_is_fine`, `fine_cvg`, `cvg_is_fine`, `cvg_EFin`, `neq0_fine_cvgP`,
    `cvgeNP`, `is_cvgeNE`, `cvge_to_ge`, `cvge_to_le`, `is_cvgeM`, `limeM`,
    `cvge_ge`, `cvge_le`, `lim_nnesum`, `ltr0_cvgV0`, `cvgrVNy`, `ler_cvg_to`,
    `gee_cvgy`, `lee_cvgNy`, `squeeze_fin`, and `lee_cvg_to`.
- in file `sequences.v`,
  + new lemma `nneseries_pinfty`.
- in file `topology.v`,
  + new lemmas `eq_cvg`, `eq_is_cvg`, `eq_near`, `cvg_toP`, `cvgNpoint`,
    `filter_imply`, `nbhs_filter`, `near_fun`, `cvgnyPgt`, `cvgnyPgty`,
    `cvgnyPgey`, `fcvg_ballP`, `fcvg_ball`, and `fcvg_ball2P`.
- in `topology.v`, added `near do` and `near=> x do` tactic notations
  to perform some tactics under a `\forall x \near F, ...` quantification.
- in `normedtype.v`, added notations `^'+`, `^'-`, `+oo_R`, `-oo_R`
- in `measure.v`:
  + definition `discrete_measurable_bool` with an instance of measurable type
  + lemmas `measurable_fun_if`, `measurable_fun_ifT`
- in `constructive_ereal.v`:
  + canonicals `maxe_monoid`, `maxe_comoid`, `mine_monoid`, `mine_comoid`
- in `mathcomp_extra.v`:
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
    `le_bigmin_nat_cond`, `le_bigmin_ord`, `le_bigmin_ord_cond`, `subset_bigmin`, and `subset_bigmin_cond`.

- in file `mathcomp_extra.v`,
  + new definitions `proj`, and `dfwith`.
  + new lemmas `dfwithin`, `dfwithout`, and `dfwithP`.
- in `measure.v`:
  + lemma `measurable_fun_bool`

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
- in `measure.v`:
  + `covered_by_countable` generalized from `pointedType` to `choiceType`

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

- in file `constructive_ereal.v`,
  + `esum_ninftyP` -> `esum_eqNyP`
  + `esum_ninfty` -> `esum_eqNy`
  + `esum_pinftyP` -> `esum_eqyP`
  + `esum_pinfty` -> `esum_eqy`
  + `desum_pinftyP` -> `desum_eqyP`
  + `desum_pinfty` -> `desum_eqy`
  + `desum_ninftyP` -> `desum_eqNyP`
  + `desum_ninfty` -> `desum_eqNy`
  + `eq_pinftyP` -> `eqyP`
- in file `lebesgue_measure.v`,
  + `measurable_fun_elim_sup` -> `measurable_fun_lim_esup`
- in file `measure.v`,
  + `caratheodory_lim_lee` -> `caratheodory_lime_le`
- in file `normedtype.v`,
  + `normmZ` -> `normrZ`
  + `norm_cvgi_map_lim` -> `norm_cvgi_lim`
  + `nbhs_image_ERFin` -> `nbhs_image_EFin`
- moved from `sequences.v` to `normedtype.v`:
  + `squeeze` -> `squeeze_cvgr`
- moved from `lebesgue_measure.v` to `real_interval.v`:
  + `itv_cpinfty_pinfty` -> `itv_cyy`
  + `itv_opinfty_pinfty` -> `itv_oyy`
  + `itv_cninfty_pinfty` -> `itv_cNyy`
  + `itv_oninfty_pinfty` -> `itv_oNyy`
- in file `sequences.v`,
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
- in file `topology.v`,
  + `cvg_map_lim` -> `cvg_lim`
  + `cvgi_map_lim` -> `cvgi_lim`
  + `app_cvg_locally` -> `cvg_ball`

### Generalized

- in file `constructive_ereal.v`,
  + `daddooe` -> `daddye`
  + `daddeoo` -> `daddey`
- moved from `normedtype.v` to `mathcomp_extra.v`:
  + `ler0_addgt0P` -> `ler_gtP`
- in file `normedtype.v`,
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

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr`, renamed `lte_spaddre`

- in file `derive.v`, deprecated
  + `ler_cvg_map` (subsumed by `ler_lim`),
- in file `normedtype.v`, deprecated
  + `cvg_distP` (use `cvgrPdist_lt` or a variation instead),
  + `cvg_dist` (use `cvg_dist_lt` or a variation instead),
  + `cvg_distW` (use `cvgrPdist_le` or a variation instead),
  + `cvg_bounded_real` (use `cvgr_norm_lty` or a variation instead),
  + `continuous_cvg_dist` (simply use the fact that `(x --> l) -> (x = l)`),
  + `cvg_dist2P` (use `cvgr2dist_ltP` or a variant instead),
  + `cvg_dist2` (use `cvgr2dist_lt` or a variant instead),
- in file `sequences.v`, deprecated
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
- in file `topology.v`, deprecated
  + `cvg_ballPpos` (use a combination of `cvg_ballP` and `posnumP`),
- in `topology.v`:
  + `cvg_dist` (use `cvgr_dist_lt` or a variation instead)

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

### Infrastructure

### Misc
