# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`
  + lemma `setC_inj`,
  + lemma `setD1K`,
  + lemma `subTset`,
  + lemma `setUidPr`, `setUidl` and `setUidr`,
  + lemma `setIidPr`, `setIidl` and `setIidr`,
  + lemma `set_fset0`, `set_fset1`, `set_fsetI`, `set_fsetU`,
  + lemma `bigcap_inf`, `subset_bigcup_r`, `subset_bigcap_r`,
  `eq_bigcupl`, `eq_bigcapl`, `eq_bigcup`, `eq_bigcap`, `bigcapIr`,
  `bigcupUr`, `bigcap_set0`, `bigcap_set1`, `bigcap0`, `bigcapT`,
  `bigcupT`, `bigcapTP`, `setI_bigcupl`, `setU_bigcapl`,
  `bigcup_mkcond`, `bigcap_mkcond`, `setC_bigsetU`, `setC_bigsetI`,
  `bigcap_set_cond`, `bigcap_set`, `bigcap_split`, `bigcap_mkord`,
  `subset_bigsetI`, `subset_bigsetI_cond`, `bigcap_image`
  + lemmas `bigcup_setU1`, `bigcap_setU1`, `bigcup_setD1`,
    `bigcap_setD1`, `bigcup_fset`, `bigcap_fset`, `bigcup_fsetU1`,
    `bigcap_fsetU1`, `bigcup_fsetD1`, `bigcap_fsetD1`,
  + defintion `mem_set : A u -> u \in A`
  + lemma `forall_sig`

- in `classical_sets.v`:
  + lemmas `bigcup_image`, `bigcup_of_set1`, `set_fset0`, `set_fset1`, `set_fsetI`,
    `set_fsetU`, `set_fsetU1`, `set_fsetD`, `set_fsetD1`,
- in `boolp.v`:
  + lemmas `orA`, `andA`
- in `measure.v`:
  + definition `seqDU`
  + lemmas `trivIset_seqDU`, `bigsetU_seqDU`, `seqDU_bigcup_eq`, `seqDUE`
- in `ereal.v`:
  + notation `x +? y` for `adde_def x y`
- in `normedtypes.v`:
  + lemma `is_intervalPlt`
- in `sequences.v`:
  + lemmas `lt_lim`, `nondecreasing_dvg_lt`, `ereal_lim_sum`
- in `ereal.v`:
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
- in `normedtype.v`:
  + lemma `mule_continuous`
- in `cardinality.v`:
  + definition `nat_of_pair`, lemma `nat_of_pair_inj`
- in `topology.v`
  + lemma `le_bigmax`
- in `real.v`:
  + lemmas `floor1`, `floor_neq0`
- in `sequences.v`:
  + lemmas `ereal_nondecreasing_opp`, `ereal_nondecreasing_is_cvg`, `ereal_nonincreasing_cvg`,
    `ereal_nonincreasing_is_cvg`
- in `normedtype.v`:
  + lemmas `ereal_is_cvgN`, `ereal_cvgZr`, `ereal_is_cvgZr`, `ereal_cvgZl`, `ereal_is_cvgZl`,
    `ereal_limZr`, `ereal_limZl`, `ereal_limN`
- in `topology.v`:
  + definition `monotonous`
  + lemma `and_prop_in`
  + lemmas `mem_inc_segment`, `mem_dec_segment`
  + lemmas `ltr_distlC`, `ler_distlC`
  + lemmas `subset_ball_prop_in_itv`, `subset_ball_prop_in_itvcc`
- in `normedtype.v`:
  + lemma `bound_itvE`
  + lemmas `nearN`, `near_in_itv`
  + lemmas `itvxx`, `itvxxP`, `subset_itv_oo_cc`
  + lemma `at_right_in_segment`
  + notations ``f @`[a, b]``, ``g @`]a , b[``
  + lemmas `mono_mem_image_segment`, `mono_mem_image_itvoo`, `mono_surj_image_segment`,
    `inc_segment_image`, `dec_segment_image`, `inc_surj_image_segment`, `dec_surj_image_segment`,
    `inc_surj_image_segmentP`, `dec_surj_image_segmentP`, ``mono_surj_image_segmentP``
- in `cardinality.v`:
  + lemmas `surjectiveE`, `surj_image_eq`, `can_surjective`
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
- in `reals.v`:
  + lemma `int_lbound_has_minimum`
  + lemma `rat_in_itvoo`
- in `topology.v`:
  + lemma `dense_rat`

### Changed

- in `classical_sets.v`
  + `setU_bigcup` -> `bigcupUl` and reversed
  + `setI_bigcap` -> `bigcapIl` and reversed
  + removed spurious disjunction in `bigcup0P`
  + `bigcup_ord` -> `bigcup_mkord` and reversed
  + `bigcup_of_set1` -> `bigcup_imset1`
- `exist_congr` -> `eq_exist` and moved from `classsical_sets.v` to
  `boolp.v`

- `predeqP` moved from `classsical_sets.v` to `boolp.v`

- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`
- in `ereal.v`:
  + change definition `mule` such that 0 x oo = 0
  + `adde` now defined using `nosimpl` and `adde_subdef`
  + `mule` now defined using `nosimpl` and `mule_subdef`
- in `real.v`:
  + generalize from `realType` to `realDomainType` lemmas
    `has_ub_image_norm`, `has_inf_supN`
- in `sequences.v`:
  + generalize from `realType` to `realFieldType` lemmas
    `cvg_has_ub`, `cvg_has_sup`, `cvg_has_inf`
- in `sequences.v`:
  + change the statements of `cvgPpinfty`, `cvgPminfty`,
    `cvgPpinfty_lt`
- in `sequences.v`:
  + generalize `nondecreasing_seqP`, `nonincreasing_seqP`, `increasing_seqP`,
    `decreasing_seqP` to equivalences
  + generalize `lee_lim`, `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`,
    `ereal_cvgD`, `ereal_limD`, `ereal_pseries0`, `eq_ereal_pseries` from `realType` to `realFieldType`
- in `topology.v`:
  + replace `closed_cvg_loc` and `closed_cvg` by a more general lemma `closed_cvg`
- move from `sequences.v` to `normedtype.v` and generalize from `nat` to `T : topologicalType`
  + lemmas `ereal_cvgN`
- in `normedtype.v`:
  + definition `is_interval`
- in `ereal.v`:
  + lemmas `lte_addl`, `lte_subl_addr`, `lte_subl_addl`, `lte_subr_addr`,
    `lte_subr_addr`, `lte_subr_addr`, `lb_ereal_inf_adherent`
- in `sequences.v`:
  + lemma `ereal_pseries_pred0` moved from `csum.v`, minor generalization
- in `landau.v`:
  + lemma `cvg_shift` renamed to `cvg_comp_shift` and moved to `normedtype.v`
- moved from `landau.v` to `normedtype.v`:
  + lemmas `comp_shiftK`, `comp_centerK`, `shift0`, `center0`, `near_shift`,
    `cvg_shift`
- lemma `exists2P` moved from `topology.v` to `boolp.v`

### Renamed

- in `classical_sets.v`
  + `eqbigcup_r` -> `eq_bigcupr`
  + `eqbigcap_r` -> `eq_bigcapr`
  + `bigcup_distrr` -> `setI_bigcupr`
  + `bigcup_distrl` -> `setI_bigcupl`
  + `bigcup_refl` -> `bigcup_splitn`
  + `setMT` -> `setMTT`

- in `classical_sets.v`:
  + generalize lemma `perm_eq_trivIset`
- in `ereal.v`:
  + `adde` -> `adde_subdef`
  + `mule` -> `mule_subdef`
- in `normedtype.v`:
  the following lemmas have been generalized to `orderType`,
  renamed as follows, moved out of the module `BigmaxBigminr`
  to `topology.v`:
  + `bigmaxr_mkcond` -> `bigmax_mkcond`
  + `bigmaxr_split` -> `bigmax_split`
  + `bigmaxr_idl` -> `bigmax_idl`
  + `bigmaxrID` -> `bigmaxID`
  + `bigmaxr_seq1` -> `bigmax_seq1`
  + `bigmaxr_pred1_eq` -> `bigmax_pred1_eq`
  + `bigmaxr_pred1` -> `bigmax_pred1`
  + `bigmaxrD1` -> `bigmaxD1`
  + `ler_bigmaxr_cond`  -> `ler_bigmax_cond `
  + `ler_bigmaxr` -> `ler_bigmax`
  + `bigmaxr_lerP` -> `bigmax_lerP`
  + `bigmaxr_sup` -> `bigmax_sup`
  + `bigmaxr_ltrP` -> `bigmax_ltrP`
  + `bigmaxr_gerP` -> `bigmax_gerP`
  + `bigmaxr_eq_arg` -> `bigmax_eq_arg`
  + `bigmaxr_gtrP` -> `bigmax_gtrP`
  + `eq_bigmaxr` -> `eq_bigmax`
- in `normedtype.v`:
  * module `BigmaxBigminr` -> `Bigminr`
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
- in `csum.v`:
  + lemma `ub_ereal_sup_adherent_img`

### Infrastructure

### Misc
