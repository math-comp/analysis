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
- in `ereal.v`:
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
- in `classical_sets.v`:
  + notation `` [set` i] ``
  + notations `set_itv`, `` `[a, b] ``, `` `]a, b] ``, `` `[a, b[ ``,
    `` `]a, b[ ``, `` `]-oo, b] ``, `` `]-oo, b[ ``, `` `[a, +oo] ``,
    `` `]a, +oo] ``, `` `]-oo, +oo[ ``
- in `cardinality.v`:
  + definitions `pair_of_nat`, `nat_of_rat`, `rat_of_nat`
  + lemmas `pair_of_rat_inj`, `countable_rat`, `nat_of_rat_inj`, `nat_of_ratK`

### Changed

### Renamed

### Removed

### Infrastructure

### Misc
