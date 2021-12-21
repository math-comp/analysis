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
    `pmule_rgt0`, `pmule_lgt0`, `nmule_lgt0`, `nmule_rgt0`
- in `measure.v`:
  + hints for `measurable0` and `measurableT`
- in `ereal.v`:
  + lemmas `muleBr`, `muleBl`
  + lemma `eqe_absl`
  + lemma `lee_pmul`
  + lemmas `cover_restr`, `eqcover_r`
- in `topology.v` : 
  + lemmas `cstE`, `compE`, `opprfunE`, `addrfunE`, `mulrfunE`, `scalrfunE`, `exprfunE`
  + multi-rule `fctE`
- in `normedtype.v`
  + lemmas `continuous_shift`, `continuous_withinNshiftx`
- in `derive.v`
  + lemmas `derive1_comp`, `derivable_cst`, `derivable_id`, trigger_derive`
  + instances `is_derive_id`, `is_derive_Nid`
- in `sequences.v`:
  + lemmas `cvg_series_bounded`, `cvg_to_0_linear`, `lim_cvg_to_0_linear`.
  + lemma `cvg_sub0`
  + lemma `cvg_zero`
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
  + lemmas `cosK`, `sin_acos`, `near_lift`, `continuous_acos`, `is_derive1_acos`
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
