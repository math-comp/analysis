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
- file `classical/mathcomp_extra.v`
- in file `classical/mathcomp_extra.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (from `classical_sets.v`)
  + definition `olift` (from `mathcomp_extra.v`)
  + definition `pred_oapp` (from `mathcomp_extra.v`)
  + definition `mul_fun` and notation `f \* g` (from `mathcomp_extra.v`)
  + lemmas `all_sig2_cond`, `oapp_comp`, `olift_comp`, `compA`,
    `can_in_pcan`, `pcan_in_inj`, `ocan_in_comp`,
    `eqbRL` (from `mathcomp_extra.v`)
  + definition `opp_fun` and notation `\- f` (from `mathcomp_extra.v`)
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
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`, `disjoint_itv`
    (from `set_interval.v`)
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itv_cc`,
    `set_itvco`, `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`,
    `set_itv_infty_infty`, `set_itv_o_infty`, `set_itv_c_infty`, `set_itv_infty_o`,
    `set_itv_infty_c`, `set_itv_pinfty_bnd`, `set_itv_bnd_ninfty`, `setUitv1`,
    `setU1itv`, `set_itvI`, `neitvE`, `neitvP`, `setitv0`, `has_lbound_itv`,
    `has_ubound_itv`, `hasNlbound`, `hasNubound`, `opp_itv_bnd_infty`, `opp_itvoo`,
    `setCitvl`, `setCitvr`, `set_itv_splitI`, `setCitv`, `set_itv_splitD`,
    `set_itv_ge`, `trivIset_set_itv_nth`, `disjoint_itvxx`, `lt_disjoint`,
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (from `set_interval.v`)
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (from `reals.v`)
- in file `classical/mathcomp_extra.v`:
  + coercion `pair_of_interval` (from `mathcomp_extra.v`)
  + definition `miditv` (from `mathcomp_extra.v`)
  + lemmas `ltBside`, `leBside`, `ltBRight`, `leBRight`, `bnd_simp`,
    `itv_splitU1`, `itv_split1U`, `mem_miditv`, `miditv_le_left`,
    `miditv_ge_right`, `predC_itvl`, `predC_itvr`, `predC_itv`
    (from `mathcomp_extra.v`)
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

### Changed
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

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr`, renamed `lte_spaddre`

### Removed

- in file `classical_sets.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (moved to `classical/mathcomp_extra.v`)
- in file `mathcomp_extra.v`:
  + definition `olift` (moved to `classical/mathcomp_extra.v`)
  + definition `pred_oapp` (moved to `classical/mathcomp_extra.v`)
  + definition `mul_fun` and notation `f \* g` (moved to `classical/mathcomp_extra.v`)
  + lemmas `all_sig2_cond`, `oapp_comp`, `olift_comp`, `compA`,
    `can_in_pcan`, `pcan_in_inj`, `ocan_in_comp`, `eqbRL` (moved to
    `classical/mathcomp_extra.v`)
  + definition `opp_fun` and notation `\- f` (moved to `classical/mathcomp_extra.v`)
- in file `fsbigop.v`:
  + notation `\sum_(_ \in _) _` (moved to `ereal.v`)
  + lemma `lee_fsum_nneg_subset`, `lee_fsum`, `ge0_mule_fsumr`,
    `ge0_mule_fsuml`, `fsume_ge0`, `fsume_le0`, `fsume_gt0`,
    `fsume_lt0`, `pfsume_eq0` (moved to `ereal.v`)
  + lemma `pair_fsum` (subsumed by `pair_fsbig`)
  + lemma `exchange_fsum` (subsumed by `exchange_fsbig`)
- in file `mathcomp_extra.v`:
  + coercion `pair_of_interval` (moved to `classical/mathcomp_extra.v`)
  + definition `miditv` (moved to `classical/mathcomp_extra.v`)
  + lemmas `ltBside`, `leBside`, `ltBRight`, `leBRight`, `bnd_simp`,
    `itv_splitU1`, `itv_split1U`, `mem_miditv`, `miditv_le_left`,
    `miditv_ge_right`, `predC_itvl`, `predC_itvr`, `predC_itv`
    (moved to `classical/mathcomp_extra.v`)
- in file `reals.v`:
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (moved to `classical/set_interval.v`)
- in file `set_interval.v`:
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`, `disjoint_itv`
    (moved to `classical/set_interval.v`)
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itv_cc`,
    `set_itvco`, `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`,
    `set_itv_infty_infty`, `set_itv_o_infty`, `set_itv_c_infty`, `set_itv_infty_o`,
    `set_itv_infty_c`, `set_itv_pinfty_bnd`, `set_itv_bnd_ninfty`, `setUitv1`,
    `setU1itv`, `set_itvI`, `neitvE`, `neitvP`, `setitv0`, `has_lbound_itv`,
    `has_ubound_itv`, `hasNlbound`, `hasNubound`, `opp_itv_bnd_infty`, `opp_itvoo`,
    `setCitvl`, `setCitvr`, `set_itv_splitI`, `setCitv`, `set_itv_splitD`,
    `set_itv_ge`, `trivIset_set_itv_nth`, `disjoint_itvxx`, `lt_disjoint`,
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (moved to `classical/set_interval.v`)

### Infrastructure

### Misc
