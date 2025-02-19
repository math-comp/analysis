# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

- in `Rstruct.v`
  + instantiate `GRinv.inv` by `Rinv` instead of `Rinvx`

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
- in `normedtype.v`
  + global hint to automatically apply `interval_open`

- in `sequences.v`:
  + lemma `seqDUE`
  + lemma `nondecreasing_telescope_sumey`

- in `ftc.v`:
  + lemma `ge0_continuous_FTC2y`
  + lemma `Rintegral_ge0_continuous_FTC2y`
  + lemma `le0_continuous_FTC2y`
- in `mathcomp_extra.v`
  + lemmas `comparable_BSide_min`, `BSide_min`, `BSide_max`,
    `real_BSide_min`, `real_BSide_max`, `natr_min`, `natr_max`,
    `comparable_min_le_min`, `comparable_max`, `min_le_min`,
    `max_le_max` and `real_sqrtC`

- new file `measurable_realfun.v`
  + with as contents the first half of the file `lebesgue_measure.v`
- in `interval_inference.v`
  + definitions `ItvReal` and `Itv01`
  + lemmas `cmp0`, `neq0`, `eq0F`, `num_min`, `num_max`
  + notation `%:num`
  + notations `{posnum R}`, `{nonneg R}`, `%:pos`, `%:nng`,
    `%:posnum`, `%:nngnum`, `[gt0 of _]`, `[lt0 of _]`, `[ge0 of _]`,
    `[le0 of _]`, `[cmp0 of _]`, `[neq0 of _]`
  + definitions `PosNum` and `NngNum`

- in `constructive_ereal.v`
  + lemmas `cmp0y`, `cmp0Ny`, `real_miney`, `real_minNye`, `real_maxey`, `real_maxNye`,
    `oppe_cmp0`, `real_fine`, `real_muleN`, `real_mulNe`, `real_muleNN`
  + definition `ext_num_sem`
  + lemmas `ext_num_num_sem`, `ext_num_num_spec`, `le_map_itv_bound_EFin`,
    `map_itv_bound_EFin_le_BLeft`, `BRight_le_map_itv_bound_EFin`,
    `le_ext_num_itv_bound`, `ext_num_spec_sub`
  + definition `ext_widen_itv`
  + lemmas `gt0e`, `lte0`, `ge0e`, `lee0`, `cmp0e`, `neqe0`
  + lemmas `ext_num_spec_pinfty`
  + canonicals `pinfty_inum`, `oppe_inum`, `EFin_inum`, `fine_inum`,
    `oppe_inum`, `adde_inum`, `dEFin_inum`, `dadde_inum`
  + lemmas `ext_num_spec_ninfty`, `ext_num_spec_EFin`, `num_spec_fine`,
    `ext_num_sem_y`, `ext_num_sem_Ny`, `oppe_boundr`, `oppe_boundl`,
    `ext_num_spec_opp`, `ext_num_spec_add`, `ext_num_spec_dEFin`,
    `ext_num_spec_dadd`
  + variant `ext_sign_spec`
  + lemmas `ext_signP`, `ext_num_itv_mul_boundl`, `ext_num_itv_mul_boundr_pos`,
    `ext_num_itv_mul_boundr`, `comparable_ext_num_itv_bound`,
    `ext_num_itv_bound_min`, `ext_num_itv_bound_max`, `ext_num_spec_mul`
  + canonicals `mule_inum`, `abse_inum`, `ext_min_max_typ`
  + definition `abse_itv`
  + lemmas `ext_num_spec_abse`, `ext_min_itv_boundr_spec`, `ext_num_spec_min`,
    `ext_max_itv_boundl_spec`, `ext_max_itv_boundr_spec`, `ext_num_spec_max`
- in `ereal.v`:
  + lemmas `ext_num_spec_ereal_sup`, `ext_num_spec_ereal_inf`
  + canonicals `ereal_sup_inum`, `ereal_inf_inum`

- in `interval_inference.v`
  + definitions `Itv.t`, `Itv.sub`, `Itv.num_sem`, `Itv.nat_sem`,
    `Itv.real1`, `Itv.real2`, `TypInstances.real_domain_typ`,
    `TypInstances.real_field_typ`, `TypInstances.nat_typ`, `ItvNum`,
    `ItvReal` and `Itv01`
  + definitions `IntItv.min`, `IntItv.max`, `Instances.min_max_typ`,
    `Instances.min_typ_inum`, `Instances.max_typ_inum`,
    `Instances.num_min_max_typ`, `Instances.natmul_inum`,
    `Instances.intmul_inum`, `IntItv.keep_pos_bound`,
    `IntItv.keep_neg_bound`, `Instances.inv_inum`,
    `IntItv.exprn_le1_bound`, `IntItv.exprn`, `Instances.exprn_inum`,
    `Instances.norm_inum`, `Instances.sqrt_itv`,
    `Instances.sqrt_inum`, `Instances.sqrtC_itv`,
    `Instances.sqrtC_inum`, `Instances.zero_inum`,
    `Instances.succn_inum`, `Instances.addn_inum`,
    `Instances.double_inum`, `Instances.muln_inum`,
    `Instances.expn_inum`, `Instances.minn_inum`,
    `Instances.maxn_inum`, `Instances.nat_min_max_typ`,
    `Instances.Posz_inum`, `Instances.Negz_inum`,
    `IntItv.keep_nonneg_bound`, `IntItv.keep_nonpos_bound`,
    `IntItv.keep_sign`, `IntItv.keep_nonpos`, `IntItv.keep_nonneg`
  + lemmas `Itv.spec_real1`, `Itv.spec_real2`,
    `TypInstances.real_domain_typ_spec`,
    `TypInstances.real_field_typ_spec`, `TypInstances.nat_typ_spec`,
    `top_wider_anything`, `real_wider_anyreal`, `le_num_itv_bound`,
    `num_itv_bound_le_BLeft`, `BRight_le_num_itv_bound`,
    `num_spec_sub`, `cmp0`, `neq0`, `eq0F`, `map_itv_bound_comp`,
    `map_itv_comp`, `inum_min`, `inum_max`, `num_le_max`,
    `num_ge_max`, `num_le_min`, `num_ge_min`, `num_lt_max`,
    `num_gt_max`, `num_lt_min`, `num_gt_min`, `itvnum_subdef`,
    `itvreal_subdef`, `itv01_subdef`
  + lemmas `Instances.num_spec_min`, `Instances.num_spec_max`,
    `Instances.nat_num_spec`, `Instances.num_spec_natmul`,
    `Instances.num_spec_int`, `Instances.num_spec_intmul`,
    `Instances.num_itv_bound_keep_pos`,
    `Instances.num_itv_bound_keep_neg`, `Instances.num_spec_inv`,
    `Instances.num_itv_bound_exprn`, `Instances.num_spec_exprn`,
    `Instances.num_spec_norm`, `num_abs_le`, `num_abs_lt`,
    `Instances.num_spec_sqrt`, `Instances.num_spec_sqrtC`,
    `Instances.nat_spec_zero`, `Instances.nat_spec_succ`,
    `Instances.nat_spec_add`, `Instances.nat_spec_double`,
    `Instances.nat_spec_mul`, `Instances.nat_spec_exp`,
    `Instances.nat_spec_min`, `Instances.nat_spec_max`,
    `Instances.num_spec_Posz`, `Instances.num_spec_Negz`
  + notation `%:num`
  + notations `{posnum R}`, `{nonneg R}`, `%:pos`, `%:nng`,
    `%:posnum`, `%:nngnum`, `[gt0 of _]`, `[lt0 of _]`, `[ge0 of _]`,
    `[le0 of _]`, `[cmp0 of _]`, `[neq0 of _]`
  + definitions `PosNum`, `NngNum`, `posnum_spec` and `nonneg_spec`
  + lemmas `posnumP` and `nonnegP`

- in `derive.v`:
  + lemmas `near_eq_derivable`, `near_eq_derive`, `near_eq_is_derive`
- in `derive.v`:
  + lemmas `derive1N`, `derivable_opp`, `derive1_id`

- in `normedtype.v`:
  + lemmas `cvg_compNP`, `decreasing_itvNyo_bigcup`, `decreasing_itvoo_bigcup`,
    `increasing_itvNyo_bigcup`, `increasing_itvoc_bigcup`

- in `num_topology.v`:
  + lemmas `lt_nbhsl`, `Nlt_nbhsl`

- in `measurable_realfun.v`:
  + lemmas `measurable_fun_itv_bndo_bndc`, `measurable_fun_itv_obnd_cbnd`

- in `real_interval.v`:
  + lemma `itv_bndy_bigcup_BLeft_shift`

- in `realfun.v`:
  + definitions `derivable_Nyo_continuous_bnd`, `derivable_oy_continuous_bnd `

- in `ftc.v`:
  + lemmas
    `decreasing_ge0_integration_by_substitutiony`,
    `ge0_integration_by_substitutionNy`,
    `increasing_ge0_integration_by_substitutiony`,
    `ge0_integration_by_substitutionNy`,
    `increasing_ge0_integration_by_substitutionT`,
    `ge0_symfun_integralT`

- in `gauss_integral`:
  + lemmas `integralT_gauss`, `integrableT_gauss`

- in `probability.v`:
  + definition `normal_pdf`
  + lemmas `normal_pdf_ge0`, `normal_pdf_gt0`, `measurable_normal_pdf`,
    `continuous_normal_pdf`, `normal_pdf_ub`
  + definition `normal_prob`, equipped with the structure of probability measure
  + lemmas `integral_normal_pdf`, `normal_prob_dom`

- in `realfun.v`:
  + lemma `cvg_addrr_Ny`

- in `normedtype.v`:
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`

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

- file `lebesgue_measure.v`
  + first half moved to a new file `measurable_realfun.v`

- file `interval_inference.v`
  + definitions `Itv.def`, `Itv.spec`, `Itv.typ`, `empty_itv`
- in `measure.v`:
  + `content_snum` -> `content_inum`
  + `measure_snum` -> `measure_inum`

### Renamed

- file `itv.v` to `interval_inference.v`

- in `interval_inference.v`
  + `opp_itv_bound_subdef` -> `IntItv.opp_bound`
  + `opp_itv_bound_subdef` -> `IntItv.opp_bound`
  + `opp_itv_ge0_subproof` -> `IntItv.opp_bound_ge0`
  + `opp_itv_gt0_subproof` -> `IntItv.opp_bound_gt0`
  + `opp_itv_subdef` -> `IntItv.opp`
  + `add_itv_boundl_subdef` -> `IntItv.add_boundl`
  + `add_itv_boundr_subdef` -> `IntItv.add_boundr`
  + `add_itv_subdef` -> `IntItv.add`
  + `itv_bound_signl` -> `IntItv.sign_boundl`
  + `itv_bound_signr` -> `IntItv.sign_boundr`
  + `interval_sign` -> `IntItv.sign`
  + `interval_sign` -> `IntItv.sign`
  + `mul_itv_boundl_subdef` -> `IntItv.mul_boundl`
  + `mul_itv_boundr_subdef` -> `IntItv.mul_boundr`
  + `mul_itv_boundrC_subproof` -> `IntItv.mul_boundrC`
  + `mul_itv_subdef` -> `IntItv.mul`
  + `Itv.top_typ_subproof` -> `TypInstances.top_typ_spec`
  + `itv_top_typ` -> `TypInstances.itv_top_typ`
  + `typ_inum_subproof` -> `TypInstances.typ_inum_spec`
  + `typ_inum` -> `TypInstances.typ_inum`
  + `zero_inum` -> `Instances.zero_inum`
  + `one_inum` -> `Instances.one_inum`
  + `opp_itv_boundl_subproof` -> `Instances.one_boundl`
  + `opp_itv_boundr_subproof` -> `Instances.one_boundr`
  + `opp_inum_subproof` -> `Instances.num_spec_opp`
  + `opp_inum` -> `Instances.opp_inum`
  + `add_inum_subproof` -> `Instances.num_spec_add`
  + `add_inum` -> `Instances.add_inum`
  + `interval_sign_spec` -> `Instances.sign_spec`
  + `interval_signP` -> `Instances.signP`
  + `mul_itv_boundl_subproof` -> `Instances.num_itv_mul_boundl`
  + `mul_itv_boundr_subproof` -> `Instances.num_itv_mul_boundr`
  + `mul_itv_boundr'_subproof` -> `Instances.BRight_le_mul_boundr`
  + `map_itv_bound_min` -> `Instances.num_itv_bound_min`
  + `map_itv_bound_max` -> `Instances.num_itv_bound_max`
  + `mul_inum_subproof` -> `Instances.num_spec_mul`
  + `mul_inum` -> `Instances.mul_inum`

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
  
- in `interval_inference.v`
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
  + `Itv.map_itv_bound` -> `map_itv_bound`
  + `Itv.map_itv` -> `map_itv`
  + `inum_eq` -> `num_eq`
  + `inum_le` -> `num_le`
  + `inum_lt` -> `num_lt`
  + `inum_min` -> `num_min`
  + `inum_max` -> `num_max`
- in `real_interval.v`:
  + `itv_bnd_infty_bigcup` -> `itv_bndy_bigcup_BRight`
  + `itv_bnd_infty_bigcup0S` -> `itv0y_bigcup0S`
  + `itv_infty_bnd_bigcup` -> `itvNy_bnd_bigcup_BLeft`

- in `set_interval.v`:
  + `opp_itv_bnd_infty` -> `opp_itv_bndy`
  + `opp_itv_infty_bnd` -> `opp_itvNy_bnd`

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

- in `ftc.v`:
  + lemmas `increasing_cvg_at_right_comp`,
    `increasing_cvg_at_left_comp`,
    `decreasing_cvg_at_right_comp`,
    `decreasing_cvg_at_left_comp`

### Deprecated
- in `Rstruct.v`
  + lemma `Rinvx`

- in `interval_inference.v`:
- file `signed.v` (use `interval_inference.v` instead)

- in `itv.v`:
  + notation `%:inum` (use `%:num` instead)

- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_itv_co`, `measurable_fun_itv_oc`

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
- in `normedtype.v`:
  + notations `cvg_distP`, `cvg_distW`, `continuous_cvg_dist`, `cvg_dist2P`,
    `cvg_gt_ge`, `cvg_lt_le_`, `linear_bounded0`
    (were deprecated since 0.6.0)
  + lemmas `__deprecated__cvg_distW`, `__deprecated__continuous_cvg_dist`,
    `__deprecated__cvg_gt_ge`, `__deprecated__cvg_lt_le`,
    `__deprecated__linear_bounded0`
    (were deprecated since 0.6.0)

- in `interval_inference.v`
  + reserved notations `[lb of _]`, `[ub of _]`, `[lbe of _]` and `[ube of _]`
    (they were unused)
  + definitions `wider_itv`
  + `Itv.subitv_map_itv` (use `num_spec_sub` instead)
  + lemma `le_map_itv_bound` (use `le_num_itv_bound` instead)
  + lemmas `opp_itv_le0_subproof`, `opp_itv_lt0_subproof`

- in `constructive_ereal.v`:
  + lemmas `num_abse_le`, `num_abse_lt`
  + canonicals `abse_snum`, `mule_snum`, `dadde_snum`, `dEFin_snum`,
    `adde_snum`, `oppe_snum`, `fine_snum`, `EFin_snum`, `ninfty_snum`,
    `pinfty_snum`

### Infrastructure

### Misc
