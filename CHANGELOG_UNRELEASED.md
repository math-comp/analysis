# Changelog (unreleased)

## [Unreleased]

### Added

- in `mathcomp_extra.v`:
  + lemmas `prodr_ile1`, `nat_int`

- in `normedtype.v`:
  + lemma `scaler1`

- in `derive.v`:
  + lemmas `horner0_ext`, `hornerD_ext`, `horner_scale_ext`, `hornerC_ext`,
    `derivable_horner`, `derivE`, `continuous_horner`
  + instance `is_derive_poly`

- in `lebesgue_integral.v`:
  + lemmas `integral_fin_num_abs`, `Rintegral_cst`, `le_Rintegral`

- new file `pi_irrational.v`:
  + lemmas `measurable_poly`
  + definition `rational`
  + module `pi_irrational`
  + lemma `pi_irrationnal`

- in `numfun.v`
  + lemmas `funeposE`, `funenegE`, `funepos_comp`, `funeneg_comp`

- in `classical_sets.v`:
  + lemmas `xsectionE`, `ysectionE`

- in `topology_theory/topological_structure.v`
  + lemmas `interior_id`, `interiorT`, `interior0`, `closureT`

- in `normedtype.v`:
  + lemma `nbhs_right_leftP`
- in `lebesgue_integral.v`:
  + lemma `integral_bigsetU_EFin`
  + lemmas `interior_itv_bnd`, `interior_itv_bndy`, `interior_itv_Nybnd`,
    definition `interior_itv`
  + lemma `interior_set1`
  + lemmas `interior_itv_bnd`, `interior_itv_bndy`, `interior_itv_Nybnd`, `interior_itv_Nyy`
  + definition `interior_itv`

- in `derive.v`:
  + lemmas `decr_derive1_le0`, `decr_derive1_le0_itv`,
           `decr_derive1_le0_itvy`, `decr_derive1_le0_itvNy`,
           `incr_derive1_ge0`, `incr_derive1_ge0_itv`,
           `incr_derive1_ge0_itvy`, `incr_derive1_ge0_itvNy`,
  + lemmas `ler0_derive1_nincry`, `ger0_derive1_ndecry`,
           `ler0_derive1_nincrNy`, `ger0_derive1_ndecrNy`
  + lemmas `ltr0_derive1_decr`, `gtr0_derive1_incr`
- in `mathcomp_extra.v`:
  + lemmas `size_filter_gt0`, `ltr_sum`, `ltr_sum_nat`

- in `classical_sets.v`:
  + lemma `itv_sub_in2`

- in `realfun.v`:
  + definition `discontinuity`
  + lemmas `nondecreasing_fun_sum_le`, `discontinuty_countable`
- in `constructive_ereal.v`:
  + lemma `abse_EFin`

- in `normedtype.v`:
  + lemmas `bounded_cst`, `subr_cvg0`

- in `lebesgue_integral.v`:
  + lemma `RintegralB`

- in `ftc.v`:
  + lemmas `differentiation_under_integral`, `derivable_under_integral`
  + definition `partial1of2`, lemma `partial1of2E`

- in `real_interval.v`:
  + lemma `itv_bnd_infty_bigcup0S`

- in `lebesgue_integral.v`:
  + lemma `ge0_cvgn_integral`

- in `trigo.v`:
  + lemma `derivable_atan`

- in `normedtype.v`:
  + lemma `cvgr_expr2`, `cvgr_idn`

- new file `gauss_integral.v`:
  + definition `oneDsqr`
  + lemmas `oneDsqr_gt0`, `oneDsqr_ge0`, `oneDsqr_ge1`, `oneDsqr_neq0`,
    `oneDsqrV_le1`, `continuous_oneDsqr`, `continuous_oneDsqrV`,
    `integral01_oneDsqr`
  + canonical `oneDsqr_ge0_snum`
  + definition `gauss_fun`
  + lemmas `gauss_fun_ge0`, `gauss_le1`, `cvg_gauss_fun`, `measurable_gauss_fun`,
    `continuous_gauss_fun`
  + module `gauss_integral_proof`
  + lemma `integral0y_gauss`

- in `normedtype.v`:
  + lemmas `ninfty`, `cvgy_compNP`

- new file `measurable_realfun.v`
  + with as contents the first half of the file `lebesgue_measure.v`

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)

### Changed

### Renamed

### Generalized

### Deprecated

### Removed

- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)

- in file `topology_structure.v`, removed `discrete_sing`, `discrete_nbhs`, and `discrete_space`.
- in file `nat_topology.v`, removed `discrete_nat`.
- in file `pseudometric_structure.v`, removed `discrete_ball_center`, `discrete_topology_type`, and 
    `discrete_space_discrete`.

- in `measure.v`:
  + notation `caratheodory_lim_lee` (was deprecated since 0.6.0)

- in `lebesgue_measure.v`:
  + notations `itv_cpinfty_pinfty`, `itv_opinfty_pinfty`, `itv_cninfty_pinfty`,
    `itv_oninfty_pinfty` (were deprecated since 0.6.0)
  + lemmas `__deprecated__itv_cpinfty_pinfty`, `__deprecated__itv_opinfty_pinfty`,
    `__deprecated__itv_cninfty_pinfty`, `__deprecated__itv_oninfty_pinfty`
    (were deprecated since 0.6.0)

- in `sequences.v`:
  + notations `cvgPpinfty_lt`, `cvgPninfty_lt`, `cvgPpinfty_near`,
    `cvgPninfty_near`, `cvgPpinfty_lt_near`, `cvgPninfty_lt_near`,
    `ereal_cvgD_ninfty_ninfty`, `invr_cvg0`, `invr_cvg_pinfty`,
    `nat_dvg_real`, `nat_cvgPpinfty`, `ereal_squeeze`, `ereal_cvgD_pinfty_fin`,
    `ereal_cvgD_ninfty_fin`, `ereal_cvgD_pinfty_pinfty`, `ereal_cvgD`,
    `ereal_cvgB`, `ereal_is_cvgD`, `ereal_cvg_sub0`, `ereal_limD`,
    `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`, `ereal_lim_sum`, `ereal_cvg_abs0`,
    `ereal_cvg_ge0`, `ereal_lim_ge`, `ereal_lim_le`, `dvg_ereal_cvg`,
    `ereal_cvg_real`
    (were deprecated since 0.6.0)
  + lemmas `__deprecated__cvgPpinfty_lt`, `__deprecated__cvgPninfty_lt`,
    `__deprecated__cvgPpinfty_near`, `__deprecated__cvgPninfty_near`,
    `__deprecated__cvgPpinfty_lt_near`, `__deprecated__cvgPninfty_lt_near`,
    `__deprecated__invr_cvg0`, `__deprecated__invr_cvg_pinfty`,
    `__deprecated__nat_dvg_real`, `__deprecated__nat_cvgPpinfty`,
    `__deprecated__ereal_squeeze`, `__deprecated__ereal_cvgD_pinfty_fin`,
    `__deprecated__ereal_cvgD_ninfty_fin`, `__deprecated__ereal_cvgD_pinfty_pinfty`,
    `__deprecated__ereal_cvgD`, `__deprecated__ereal_cvgB`, `__deprecated__ereal_is_cvgD`,
    `__deprecated__ereal_cvg_sub0`, `__deprecated__ereal_limD`,
    `__deprecated__ereal_cvgM_gt0_pinfty`, `__deprecated__ereal_cvgM_lt0_pinfty`,
    `__deprecated__ereal_cvgM_gt0_ninfty`, `__deprecated__ereal_cvgM_lt0_ninfty`,
    `__deprecated__ereal_cvgM`, `__deprecated__ereal_lim_sum`,
    `__deprecated__ereal_cvg_abs0`, `__deprecated__ereal_cvg_ge0`,
    `__deprecated__ereal_lim_ge`, `__deprecated__ereal_lim_le`,
    `__deprecated__dvg_ereal_cvg`, `__deprecated__ereal_cvg_real`
    (were deprecated since 0.6.0)

- in `derive.v`:
  + notations `le0r_cvg_map`, `ler0_cvg_map`, `ler_cvg_map`
    (deprecated since 0.6.0)
  + lemmas `__deprecated__le0r_cvg_map`, `__deprecated__ler0_cvg_map`,
    `__deprecated__ler_cvg_map`
    (deprecated since 0.6.0)

- in `normedtype.v`
  + notations `cvg_distP`, `cvg_distW`, `continuous_cvg_dist`, `cvg_dist2P`,
    `cvg_gt_ge`, `cvg_lt_le_`, `linear_bounded0`
    (deprecated since 0.6.0)
  + lemmas `__deprecated__cvg_distW`, `__deprecated__continuous_cvg_dist`,
    `__deprecated__cvg_gt_ge`, `__deprecated__cvg_lt_le`,
    `__deprecated__linear_bounded0 `
    (deprecated since 0.6.0)

- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)

### Infrastructure

### Misc
