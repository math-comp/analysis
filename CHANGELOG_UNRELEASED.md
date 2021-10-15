# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `setDIr`
  + lemmas `setMT`, `setTM`, `setMI`
  + lemmas `setSM`, `setM_bigcupr`, `setM_bigcupl`
- in `ereal.v`:
  + lemma `onee_eq0`
  + lemma `EFinB`
  + lemmas `mule_eq0`, `mule_lt0_lt0`, `mule_gt0_lt0`, `mule_lt0_gt0`,
    `pmule_rge0`, `pmule_lge0`, `nmule_lge0`, `nmule_rge0`,
    `pmule_rgt0`, `pmule_lgt0`, `nmule_lgt0`, `nmule_rgt0`,
- in `measure.v`:
  + hints for `measurable0` and `measurableT`
  + notation `x +? y` for `adde_def x y`
- in `normedtypes.v`:
  + lemma `is_intervalPlt`
  + lemma `cvg_sub0`
  + lemma `cvg_zero`
- in `sequences.v`:
  + lemmas `lt_lim`, `nondecreasing_dvg_lt`, `ereal_lim_sum`
- in `ereal.v`:
  + lemmas `muleBr`, `muleBl`
  + lemma `eqe_absl`
  + lemma `lee_pmul`
  + lemmas `cover_restr`, `eqcover_r`
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
- new file `nsatz_realType`
- in `normedtype.v`
  + lemmas `continuous_shift`, `continuous_withinNshiftx`
- new file `exp.v`
  + lemma `normr_nneg` (hint)
  + lemmas `seriesN`, `seriesZr`, `seriesD`, `is_cvg_seriesN`, `lim_seriesN`, `is_cvg_seriesZr`,
    `lim_seriesZr`, `is_cvg_seriesD`, `lim_seriesD`, `is_cvg_seriesB`, `lim_seriesB`,
    `lim_series_norm`, `lim_series_le`, `cvg_to_0_linear`, `lim_cvg_to_0_linear`,
    `derive1_comp`, `is_derive1_id`, `is_derive_0_cst`
  + instance `is_derive1_comp`, `is_deriveV`
  + lemma `trigger_derive`
  + ltac `rcfE`
  + lemma `is_derive1_caratheodory`, `is_derive_inverse`, `continuous_ln`
  + instance `is_derive1_ln`
  + facts `is_cvg_series_Xn_inside_norm`, `is_cvg_series_Xn_inside`
  + definition `diffs`
  + lemmas `diffsN`, `diffs_inv_fact`, `diffs_sumE`, `diffs_equiv`, `is_cvg_diffs_equiv`, `termdiffs`
  + lemmas `expR0`, `expR_ge1Dx`, `exp_coeffE`, `expRE`
  + instance `is_derive_expR`
  + lemmas `derivable_expR`, `continuous_expR`, `expRxDyMexpx`, `expRxMexpNx_1`
  + lemmas `pexpR_gt1`, `expR_gt0`, `expRN`, `expRD`, `expRMm`
  + lemmas `expR_gt1`, `expR_lt1, `expRB`, `ltr_expR`, `ler_expR`, `expR_inj`,
    `expR_total_gt1`, `expR_total`
  + definition `ln`
  + fact `ln0`
  + lemmas `expK`, `lnK`, `ln1`, `lnM`, `ln_inj`, `lnV`, `ln_div`, `ltr_ln`, `ler_ln`, `lnX`
  + lemmas `le_ln1Dx`, `ln_sublinear`, `ln_ge0`, `ln_gt0`
  + definition `exp_fun`, notation `^
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
  + lemmas `sin_coeff'E`, `cvg_sin_coeff'`, `diffs_sin`, `series_sin_coeff0`
  + lemma `sin0`
  + definition `cos_coeff`
  + lemmas `cos_ceff_2_0`, `cos_coeff_2_2`, `cos_coeff_2_4`, `cos_coeffE`, `is_cvg_series_cos_coeff`
  + definition `cos`
  + lemma `cosE`
  + definition `cos_coeff'`
  + lemmas `cos_coeff'E`, `cvg_cos_coeff'`, `diffs_cos`, `series_cos_coeff0`, `cos0`
  + lemmas `is_derive_sin`, `derivable_sin`, `continuous_sin`, `is_derive_cos`, `derivable_cos`, `continuous_cos`
  + lemmas `cos2Dsin2`, `cosD`, `sinN`, `sinB`
  + definition `pi`
  + lemmas `pihalfE`, `cos2_lt0`, `cos_exists`
  + lemmas `pi_gt0`, `pi_ge0`
  + lemmas `ltr_cos`, `ltr_sin`, `cos_inj`, `sin_inj`
  + definition `tan`
  + lemmas `tan0`, `tanpi`
  + lemmas `tanN`, `tanD`, `tan_mulr2n`, `cos2_tan2`
  + lemmas `tan_pihalf`, `tan_piquarter`, `tanDpi`, `continuous_tan`
  + instance `is_derive_tan`
  + lemmas `derivable_tan`, `ltr_tan`, `tan_inj`
  + definition `acos`
  + lemmas `acosK`, `cosK`
  + definition `asin`
  + lemmas `asinK`, `sinK`
  + definition `atan`
  + lemmas `atanK`, `tanK`

### Changed

- in `normedtype.v`:
  + `nbhs_minfty_lt` renamed to `nbhs_ninfty_lt_pos` and changed to not use `{posnum R}`
  + `nbhs_minfty_le` renamed to `nbhs_ninfty_le_pos` and changed to not use `{posnum R}`
- in `sequences.v`:
  + lemma `is_cvg_ereal_nneg_natsum`: remove superfluous `P` parameter
  + lemma `notin_set`
- in `boolp.v`:
  + lemmas `not_True`, `not_False`
- in `topology.v`
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

### Renamed

- in `normedtype.v`:
  + `nbhs_minfty_lt_real` -> `nbhs_ninfty_lt`
  + `nbhs_minfty_le_real` -> `nbhs_ninfty_le`
- in `sequences.v`:
  + `cvgNminfty` -> `cvgNninfty`
  + `cvgPminfty` -> `cvgPninfty`
  + `ler_cvg_minfty` -> `ler_cvg_ninfty`
  + generalize `nondecreasing_seqP`, `nonincreasing_seqP`, `increasing_seqP`,
    `decreasing_seqP` to equivalences
  + generalize `lee_lim`, `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`,
    `ereal_cvgD`, `ereal_limD`, `ereal_pseries0`, `eq_ereal_pseries` from `realType` to `realFieldType`
- in `sequences.v`:
  + lemmas `cvg_series_bounded`, `cvg_to_0_linear`, `lim_cvg_to_0_linear`.
- in `topology.v`:
  + replace `closed_cvg_loc` and `closed_cvg` by a more general lemma `closed_cvg`
- move from `sequences.v` to `normedtype.v` and generalize from `nat` to `T : topologicalType`
  + lemmas `ereal_cvgN`
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
- in `normedtype.v`:
  + lemmas `bounded_fun_has_ubound`, `bounded_funN`, `bounded_fun_has_lbound`,
    `bounded_funD`
- in `reals.v`:
  + lemma `has_ub_lbN`
- in `sequences.v`:
  + lemma `ereal_is_cvgD`
  + lemma `ereal_pseries_pred0` moved from `csum.v`, minor generalization
- in `landau.v`:
  + lemma `cvg_shift` renamed to `cvg_comp_shift` and moved to `normedtype.v`
- moved from `landau.v` to `normedtype.v`:
  + lemmas `comp_shiftK`, `comp_centerK`, `shift0`, `center0`, `near_shift`,
    `cvg_shift`
- move from `derive.v` to `topology.v`: `exprfunE`
  + replace `closed_cvg_loc` and `closed_cvg` by a more general lemma `closed_cvg`
- in `topology.v` : 
  + lemmas `cstE`, `compE`, `opprfunE`, `addrfunE`, `mulrfunE`, `scalrfunE`
  + multi-rule `rcfE`

### Changed

- in `sequences.v`:
  + statements of lemmas `nondecreasing_cvg`, `nondecreasing_is_cvg`,
    `nonincreasing_cvg`, `nonincreasing_is_cvg` use `has_{l,u}bound`
    predicates instead of requiring an additional variable
  + statement of lemma `S1_sup` use `ubound` instead of requiring an
    additional variable

### Renamed

- in `sequences.v`:
  + `nondecreasing_seq_ereal_cvg` -> `ereal_nondecreasing_cvg`

### Removed

### Infrastructure

### Misc
