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
  + lemma `ge0_cvg_integral`

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

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`

- in `derive.v`:
  + put the notation ``` ^`() ``` and ``` ^`( _ ) ``` in scope `classical_set_scope`

- in `numfun.v`
  + lock `funepos`, `funeneg`

- moved from `lebesgue_integral.v` to `measure.v` and generalized
  + lemmas `measurable_xsection`, `measurable_ysection`

- moved from `topology_structure.v` to `discrete_topology.v`: 
  `discrete_open`, `discrete_set1`, `discrete_closed`, and `discrete_cvg`.

- moved from `pseudometric_structure.v` to `discrete_topology.v`:
    `discrete_ent`, `discrete_ball`, and `discrete_topology`.
- in file `cantor.v`, `cantor_space` now defined in terms of `bool`.
- in file `separation_axioms.v`, updated `discrete_hausdorff`, and
    `discrete_zero_dimension` to take a `discreteTopologicalType`.

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
- in `normedtype.v`:
  + `cvge_sub0` -> `sube_cvg0`

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
    
- in `normedtype.v`:
  + lemmas `not_near_at_rightP`, `not_near_at_leftP`

- in `Rstruct.v`:
  + lemma `RsqrtE`

### Deprecated

### Removed

- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)

- in file `topology_structure.v`, removed `discrete_sing`, `discrete_nbhs`, and `discrete_space`.
- in file `nat_topology.v`, removed `discrete_nat`.
- in file `pseudometric_structure.v`, removed `discrete_ball_center`, `discrete_topology_type`, and 
    `discrete_space_discrete`.

### Infrastructure

### Misc
