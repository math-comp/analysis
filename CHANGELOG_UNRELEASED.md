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
- in `constructive_ereal.v`:
  + lemma `abse_EFin`

- in `normedtype.v`:
  + lemmas `bounded_cst`, `cvgr_sub0`

- in `lebesgue_integral.v`:
  + lemma `RintegralB`

- in `ftc.v`:
  + lemmas `differentiation_under_integral`, `derivable_under_integral`
  + definition `partial1`, notation `'d1`

- in `real_interval.v`:
  + lemma `itv_bnd_infty_bigcup0S`

- in `lebesgue_integral.v`:
  + lemma `ge0_cvg_integral`

- in `trigo.v`:
  + lemma `derivable_atan`

- new file `gauss_integral.v`:
  + definition `oneDsqr`
  + lemmas `oneDsqr_gt0`, `oneDsqr_ge0`, `oneDsqr_ge1`, `oneDsqr_neq0`,
    `oneDsqrV_le1`, `continuous_oneDsqr`, `continuous_oneDsqrV`,
    `integral01_atan`
  + definition `gauss`
  + lemmas `gauss_ge0`, `gauss_le1`, `cvg_gauss`, `measurable_gauss`,
    `continuous_gauss`
  + module `gauss_integral_proof`
  + lemma `integral0y_gauss_pi2`

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`

- in `derive.v`:
  + put the notation ``` ^`() ``` and ``` ^`( _ ) ``` in scope `classical_set_scope`

- in `numfun.v`
  + lock `funepos`, `funeneg`

- moved from `lebesgue_integral.v` to `measure.v` and generalized
  + lemmas `measurable_xsection`, `measurable_ysection`

### Renamed

- in `measure.v`
  + `preimage_class` -> `preimage_set_system`
  + `image_class` -> `image_set_system`
  + `preimage_classes` -> `g_sigma_preimageU`
  + `preimage_class_measurable_fun` -> `preimage_set_system_measurable_fun`
  + `sigma_algebra_preimage_class` -> `sigma_algebra_preimage`
  + `sigma_algebra_image_class` -> `sigma_algebra_image`
  + `sigma_algebra_preimage_classE` -> `g_sigma_preimageE`
  + `preimage_classes_comp` -> `g_sigma_preimageU_comp`

### Generalized

- in `sequences.v`,
  + generalized indexing from zero-based ones (`0 <= k < n` and `k <oo`)
    to `m <= k < n` and `m <= k <oo`
    * lemmas `nondecreasing_series`, `ereal_nondecreasing_series`,
             `eseries_mkcondl`, `eseries_mkcondr`, `eq_eseriesl`,
	     `nneseries_lim_ge`, `adde_def_nneseries`,
	     `nneseriesD`, `nneseries_sum_nat`, `nneseries_sum`,
  + lemmas `nneseries_ge0`, `is_cvg_nneseries_cond`, `is_cvg_npeseries_cond`,
    `is_cvg_nneseries`, `is_cvg_npeseries`, `nneseries_ge0`, `npeseries_le0`,
    `lee_nneseries`
    
### Deprecated

### Removed

- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)

### Infrastructure

### Misc
