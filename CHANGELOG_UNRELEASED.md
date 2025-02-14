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
- in `mathcomp_extra.v`
  + lemmas `comparable_BSide_min`, `BSide_min`, `BSide_max`,
    `real_BSide_min`, `real_BSide_max`, `natr_min`, `natr_max`,
    `comparable_min_le_min`, `comparable_max`, `min_le_min`,
    `max_le_max` and `real_sqrtC`

- in `itv.v`
  + lemmas `cmp0`, `neq0`, `eq0F`
  + definitions `ItvReal` and `Itv01`
  + lemmas `cmp0`, `neq0`, `eq0F`, `num_min`, `num_max`
  + notation `%:num`
  + notations `{posnum R}`, `{nonneg R}`, `%:pos`, `%:nng`,
    `%:posnum`, `%:nngnum`, `[gt0 of _]`, `[lt0 of _]`, `[ge0 of _]`,
    `[le0 of _]`, `[cmp0 of _]`, `[neq0 of _]`
  + definitions `PosNum` and `NngNum`

- in `constructive_ereal.v`
  + lemmas `cmp0y`, `cmp0Ny`, `real_miney`, `real_minNye`,
    `real_maxey`, `real_maxNye`, `oppe_cmp0`, `real_fine`,
    `real_muleN`, `real_mulNe`, `real_muleNN`

### Changed

- in `lebesgue_integral.v`
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

- in `normedtype.v`:
  + lemma `cvgyNP` renamed to `cvgNy_compN` and generalized

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

- in `measure.v`:
  + `setDI_closed` -> `setD_closed`
  + `setDI_semi_setD_closed` -> `setD_semi_setD_closed`
  + `sedDI_closedP` -> `setD_closedP`
  + `setringDI` -> `setringD`

- in `lebesgue_integral.v`:
  + `Rintegral_setU_EFin` -> `Rintegral_setU`
  
- in `itv.v`
  + definition `ItvNum`

### Renamed

- in `itv.v`
  + `itv_bottom` -> `bottom`
  + `itv_gt0` -> `gt0`
  + `itv_le0F` -> `le0F`
  + `itv_lt0` -> `lt0`
  + `itv_ge0F` -> `ge0F`
  + `itv_ge0` -> `ge0`
  + `itv_lt0F` -> `lt0F`
  + `itv_le0` -> `le0`
  + `itv_gt0F` -> `gt0F`
  + `itv_top_typ` -> `top_typ`
  + `inum_eq` -> `num_eq`
  + `inum_le` -> `num_le`
  + `inum_lt` -> `num_lt`

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
- in `constructive_ereal.v`:
  + generalized from `realDomainType` to `numDomainType`
    * lemmas `EFin_min` and `EFin_max`
    * lemmas `maxye`, `maxeNy`, `mineNy`, `minye`

- in `Rstruct.v`:
  + lemma `RsqrtE`

- in `normedtype.v`:
  + `cvg_at_right_filter`, `cvg_at_left_filter`
- in `normedtype.v`
  + lemma `open_subball`
  + lemma `interval_unbounded_setT`

- in `derive.v`:
  + lemmas `decr_derive1_le0`, `incr_derive1_ge0`

- in `lebesgue_measure.v`:
  + definition `vitali_cover`, lemma `vitali_coverS`

### Deprecated

- file `signed.v` (use `itv.v` instead)

- in `itv.v`:
  + notation `%:inum` (use `%:num` instead)

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

### Infrastructure

### Misc
