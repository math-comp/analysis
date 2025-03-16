# Changelog (unreleased)

## [Unreleased]

### Added

- in `probability.v`:
  + lemmas `eq_bernoulli`, `eq_bernoulliV2`

- in `measure.v`:
  + lemmas `mnormalize_id`, `measurable_fun_eqP`

- in `ftc.v`:
  + lemma `integrable_locally`

- in `constructive_ereal.v`:
  + lemma `EFin_bigmax`

- in `mathcomp_extra.v`:
  + lemmas `inr_inj`, `inl_inj`

- in `classical_sets.v`:
  + lemmas `in_set1`, `inr_in_set_inr`, `inl_in_set_inr`, `mem_image`, `mem_range`, `image_f`
  + lemmas `inr_in_set_inl`, `inl_in_set_inl`

- in `lebesgue_integral_approximation.v` (now `measurable_fun_approximation.v`):
  + lemma `measurable_prod`
  + lemma `measurable_fun_lte`
  + lemma `measurable_fun_lee`
  + lemma `measurable_fun_eqe`
  + lemma `measurable_poweR`

- in `exp.v`:
  + lemma `poweRE`

- in `exp.v`:
  + lemmas `lnNy`, `powR_cvg0`, `derivable_powR`, `powR_derive1`
  + Instance `is_derive1_powR`
- in `realfun.v`:
  + lemma `cvge_ninftyP`

### Renamed

- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`

### Generalized

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)
  + lemmas `RabsE`, `RdistE`, `sum_f_R0E`, `factE`

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- file `constructive_ereal.v`:
  + definition `iter_mule`
  + lemma `prodEFin`

- file `exp.v`:
  + lemma `expR_sum`

- file `lebesgue_integral.v`:
  + lemma `measurable_fun_le`

- file `mathcomp_extra.v`:
  + lemma `mulr_funEcomp`

- in `numfun.v`:
  + defintions `funrpos`, `funrneg` with notations `^\+` and `^\-`
  + lemmas `funrpos_ge0`, `funrneg_ge0`, `funrposN`, `funrnegN`, `ge0_funrposE`,
    `ge0_funrnegE`, `le0_funrposE`, `le0_funrnegE`, `ge0_funrposM`, `ge0_funrnegM`,
    `le0_funrposM`, `le0_funrnegM`, `funr_normr`, `funrposneg`, `funrD_Dpos`,
    `funrD_posD`, `funrpos_le`, `funrneg_le`
  + lemmas `funerpos`, `funerneg`

- in `measure.v`:
  + lemma `preimage_class_comp`
  + defintions `preimage_display`, `g_sigma_algebra_preimageType`, `g_sigma_algebra_preimage`,
    notations `.-preimage`, `.-preimage.-measurable`

- in `measurable_realfun.v`:
  + lemmas `measurable_funrpos`, `measurable_funrneg`

- new file `independence.v`:
  + lemma `expectationM_ge0`
  + definition `independent_events`
  + definition `mutual_independence`
  + definition `independent_RVs`
  + definition `independent_RVs2`
  + lemmas `g_sigma_algebra_preimage_comp`, `g_sigma_algebra_preimage_funrpos`,
    `g_sigma_algebra_preimage_funrneg`
  + lemmas `independent_RVs2_comp`, `independent_RVs_comp`, `independent_RVs_scale`,
    `independent_RVs2_funrposneg`,
    `independent_RVs2_funrnegpos`, `independent_RVs2_funrnegneg`,
    `independent_RVs2_funrpospos`
  + lemma `expectationM_ge0`, `integrable_expectationM`, `independent_integrableM`,
    ` expectation_mul`

- in `trigo.v`:
  + lemma `integral0oo_atan`

- in `measure.v`:
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`
  + lemma `preimage_set_system_id`

- in `Rstruct_topology.v`:
  + lemma `RexpE`

- in `derive.v`:
  + lemmas `derive_shift`, `is_derive_shift`

- in `interval_inference.v`:
  + definitions `IntItv.exprz`, `Instances.natmul_itv`
  + lemmas `Instances.num_spec_exprz`, `Instances.nat_spec_factorial`
  + canonical instance `Instances.exprz_inum`,
    `Instances.factorial_inum`

- in `mathcomp_extra.v`:
  + lemmas `exprz_ge0` and `exprz_gt0`

- in `exp.v`
  + lemmas `expR_le1`, `num_spec_expR`, `num_spec_powR`
  + definitions `expR_itv_boundl`, `expR_itv_boundr`, `expR_itv`,
    `powR_itv`
  + canonical instance `expR_inum`, `powR_inum`

- in `numfun.v`:
  + lemma `num_spec_indic`
  + canonical instance `indic_inum`

- in `trigo.v`:
  + lemmas `num_spec_sin`, `num_spec_cos`
  + canonical instances `sin_inum`, `cos_inum`

- in `mathcomp_extra.v`:
  + lemmas `intrN`, `real_floor_itv`, `real_ge_floor`, `real_ceil_itv`
- in `lebesgue_integral.v`:
  + lemma `dominated_cvg` (was previous `Local`)

- in `ftc.v`:
  + lemma `continuity_under_integral`

- in `set_interval.v`:
  + lemma `subset_itv`

- in `mathcomp_extra.v`:
  + lemmas `truncn_le`, `real_truncnS_gt`, `truncn_ge_nat`,
    `truncn_gt_nat`, `truncn_lt_nat`, `real_truncn_le_nat`,
    `truncn_eq`, `le_truncn`, `real_floorD1_gt`,
    `real_floor_ge_int_tmp`, `real_floor_ge_int`, `real_floor_lt_int`,
    `le_floor`, `real_floor_eq`, `real_floor_ge0`, `floor_lt0`,
    `real_floor_le0`, `floor_gt0`, `floor_neq0`,
    `real_ceil_le_int_tmp`, `real_ceil_le_int`, `real_ceil_gt_int`,
    `real_ceil_eq`, `le_ceil_tmp`, `real_ceil_ge0`, `ceil_lt0`,
    `real_ceil_le0`, `ceil_gt0`, `ceil_neq0`, `truncS_gt`,
    `truncn_le_nat`, `floorD1_gt`, `floor_ge_int_tmp`, `floor_lt_int`,
    `floor_eq`, `floor_ge0`, `floor_le0`, `ceil_le_int`,
    `ceil_le_int_tmp`, `ceil_gt_int`, `ceil_eq`, `ceil_ge0`,
    `ceil_le0`, `natr_int`

- new directory `lebesgue_integral_theory` with new files:
  + `simple_functions.v`
  + `lebesgue_integral_definition.v`
  + `lebesgue_integral_approximation.v`
  + `lebesgue_integral_monotone_convergence.v`
  + `lebesgue_integral_nonneg.v`
  + `lebesgue_integrable.v`
  + `lebesgue_integral_dominated_convergence.v`
  + `lebesgue_integral_under.v`
  + `lebesgue_Rintegral.v`
  + `lebesgue_integral_fubini.v`
  + `lebesgue_integral_differentiation.v`
  + `lebesgue_integral.v`
- in `boolp.v`:
  + lemmas `orW`, `or3W`, `or4W`
  
- in `classical_sets.v`:
  + lemmas `set_cst`, `image_nonempty`

- in `unstable.v`:
  + lemmas `eq_exists2l`, `eq_exists2r`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`
- in `functions.v`:
  + lemma `natmulfctE`

- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`
- in `constructive_ereal.v`:
  + lemmas `expe_ge0`, `expe_eq0`, `expe_gt0`

- in `ereal.v`:
  + lemmas `ereal_sup_cst`, `ereal_inf_cst`,
    `ereal_sup_pZl`, `ereal_supZl`, `ereal_inf_pZl`, `ereal_infZl`

- in `sequences.v`:
  + lemmas `ereal_inf_seq`, `ereal_sup_seq`

### Changed

- in `pi_irrational`:
  + definition `rational`

- in `charge.v`:
  + lemma `ae_eq_mul2l`

- in `hoelder.v`
  + lemmas `Lnorm0`, `Lnorm_cst1`
  + definition `conjugate`
  + lemma `conjugateE`
  + lemmas `lerB_DLnorm`, `lerB_LnormD`, `eminkowski`
  + definition `finite_norm`
  + mixin `isLfun` with field `lfuny`
  + structure `Lfun`
  + notation `LfunType`
  + definition `Lequiv`
  + canonical `Lequiv_canonical`
  + definition `LspaceType`
  + canonicals `LspaceType_quotType`, `LspaceType_eqType`, `LspaceType_choiceType`,
    `LspaceType_eqQuotType`
  + lemma `LequivP`
  + record `LType`
  + coercion `LfunType_of_LType`
  + definition `Lspace` with notation `mu.-Lspace p`
  + lemma `lfun_integrable`, `lfun1_integrable`, `lfun2_integrable_sqr`, `lfun2M2_1`
  + lemma `lfunp_scale`, `lfun_cst`,
  + definitions `finlfun`, `lfun`, `lfun_key`
  + canonical `lfun_keyed`
  + lemmas `sub_lfun_mfun`, `sub_lfun_finlfun`
  + definition `lfun_Sub`
  + lemmas `lfun_rect`, `lfun_valP`, `lfuneqP`, `lfuny0`, `mfunP`, `lfunP`,
    `mfun_scaler_closed`
  + lemmas `LnormZ`, `lfun_submod_closed`
  + lemmas `finite_norm_fine`, `ler_LnormD`,
    `LnormrN`, `Lnormr_natmul`, `fine_Lnormr_eq0`
  + lemma `Lspace_inclusion`
    `LnormN`, `Lnorm_natmul`, `fine_Lnorm_eq0`
  + lemma `lfun_inclusion`, `lfun_inclusion12`
  + lemma `lfun_oppr_closed`
  + lemma `lfun_addr_closed`

- in `simple_functions.v`:
  + lemma `mfunMn`

- in `measure.v`:
  + lemmas `seqDU_measurable`, `measure_gt0`
  + notation `\forall x \ae mu , P`
  + notations `f = g %[ae mu in D ]`, `f = g %[ae mu ]`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`
  + instances `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
  + lemmas `ae_eq_comp2`, `ae_foralln`

- new file `ess_sup_inf.v`:
  + lemma `measure0_ae`
  + definition `ess_esup`
  + lemmas `ess_supEae`, `ae_le_measureP`, `ess_supEmu0`, `ess_sup_ge`,
    `ess_supP`, `le_ess_sup`, `eq_ess_sup`, `ess_sup_cst`, `ess_sup_ae_cst`,
    `ess_sup_gee`, `abs_sup_eq0_ae_eq`, `abs_ess_sup_eq0`, `ess_sup_pZl`,
    `ess_supZl`, `ess_sup_eqNyP`, `ess_supD`, `ess_sup_absD`
  + notation `ess_supr`
  + lemmas `ess_supr_bounded`, `ess_sup_eqr0_ae_eq`, `ess_suprZl`,
    `ess_sup_ger`, `ess_sup_ler`, `ess_sup_cstr`, `ess_suprD`, `ess_sup_normD`
  + definition `ess_inf`
  + lemmas `ess_infEae`, `ess_infEN`, `ess_supEN`, `ess_infN`, `ess_supN`,
    `ess_infP`, `ess_inf_le`, `le_ess_inf`, `eq_ess_inf`, `ess_inf_cst`,
    `ess_inf_ae_cst`, `ess_inf_gee`, `ess_inf_pZl`, `ess_infZl`, `ess_inf_eqyP`,
    `ess_infD`
  + notation `ess_infr`
  + lemmas `ess_infr_bounded`, `ess_infrZl`, `ess_inf_ger`, `ess_inf_ler`,
    `ess_inf_cstr`

- in `nat_topology.v`:
  + lemma `nbhs_infty_gtr`

- in `hoelder.v`:
  + lemmas `poweR_Lnorm`, `oppe_Lnorm`
- in `probability.v`:
  + lemma `lfun1_expectation_lty`
- in `derive.v`:
  + lemmas `derive_shift`, `is_derive_shift`

- in `hoelder.v`:
  + lemmas `Lnorm_eq0_eq0`

- in `lebesgue_integral.v`:
  + lemmas `ae_eq_integral_abs`, `ge0_ae_eq_integral`, `ae_eq_integral`

- in `measurable.v`
  + from instance to definitions: `ae_filter_ringOfSetsType`, `ae_properfilter_algebraOfSetsType`
  + definiton `ae_eq`
  + definition `ess_sup` moved to `ess_sup_inf.v`

- in `probability.v`
  + lemma `expectation_fin_num`, `expectationZl`, `expectationD`, `expectationB`, `expectation_sum`,
    `covarianceE`, `covariance_fin_num`, `covarianceZl`, `covarianceZr`, `covarianceNl`,
    `covarianceNr`, `covarianceNN`, `covarianceDl`, `covarianceDr`, `covarianceBl`, `covarianceBr`,
     `varianceE`, `variance_fin_num`, `varianceZ`, `varianceN`, `varianceD`, `varianceB`,
     `varianceD_cst_l`, `varianceD_cst_r`, `varianceB_cst_l`, `varianceB_cst_r`, `covariance_le`

### Renamed

- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`

- in `lebesgue_integral_approximation.v`:
  + `emeasurable_fun_lt` -> `measurable_lte`
  + `emeasurable_fun_le` -> `measurable_lee`
  + `emeasurable_fun_eq` -> `measurable_lee`
  + `emeasurable_fun_neq` -> `measurable_neqe`

- file `lebesgue_integral_approximation.v` -> `measurable_fun_approximation.v`
- in `mathcomp_extra.v`
  + `comparable_min_le_min` -> `comparable_le_min2`
  + `comparable_max_le_max` -> `comparable_le_max2`
  + `min_le_min` -> `le_min2`
  + `max_le_max` -> `le_max2`
  + `real_sqrtC` -> `sqrtC_real`
- in `measure.v`
  + `preimage_class` -> `preimage_set_system`
  + `image_class` -> `image_set_system`
  + `preimage_classes` -> `g_sigma_preimageU`
  + `preimage_class_measurable_fun` -> `preimage_set_system_measurable_fun`
  + `sigma_algebra_preimage_class` -> `sigma_algebra_preimage`
  + `sigma_algebra_image_class` -> `sigma_algebra_image`
  + `sigma_algebra_preimage_classE` -> `g_sigma_preimageE`
  + `preimage_classes_comp` -> `g_sigma_preimageU_comp`
  
### Renamed

- in `lebesgue_measure.v`:
  + `measurable_fun_indic` -> `measurable_indic`
  + `emeasurable_fun_sum` -> `emeasurable_sum`
  + `emeasurable_fun_fsum` -> `emeasurable_fsum`
  + `ge0_emeasurable_fun_sum` -> `ge0_emeasurable_sum`
- in `probability.v`:
  + `expectationM` -> `expectationZl`

- in `classical_sets.v`:
  + `preimage_itv_o_infty` -> `preimage_itvoy`
  + `preimage_itv_c_infty` -> `preimage_itvcy`
  + `preimage_itv_infty_o` -> `preimage_itvNyo`
  + `preimage_itv_infty_c` -> `preimage_itvNyc`

- in `constructive_ereal.v`:
  + `maxeMr` -> `maxe_pMr`
  + `maxeMl` -> `maxe_pMl`
  + `mineMr` -> `mine_pMr`
  + `mineMl` -> `mine_pMl`

- in `probability.v`:
  + `integral_distribution` -> `ge0_integral_distribution`

- file `homotopy_theory/path.v` -> `homotopy_theory/continuous_path.v`

- in `ereal.v`:
  + `ereal_sup_le` -> `ereal_sup_ge`

- in `pseudometric_normed_Zmodule.v`:
  + `opp_continuous` -> `oppr_continuous`

### Generalized

- in `normedtype.v`:
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`
- in `functions.v`:
  + `fct_sumE`, `addrfctE`, `sumrfctE` (from `zmodType` to `nmodType`)
  + `scalerfctE` (from `pointedType` to `Type`)

- in `measurable_realfun.v`
  + lemma `measurable_ln`

- in `hoelder.v`:
  + `minkowski` -> `minkowski_EFin`

- in `hoelder.v`:
  + definition `Lnorm` generalized to functions with codomain `\bar R`
    (this impacts the notation `'N_p[f]`)
  + lemmas `Lnorm1`, `eq_Lnorm` (from `f : _ -> R` to `f : _ -> \bar R`)

- in `probability.v`
  + lemma `cantelli`

### Deprecated

### Removed

- in `functions.v`:
  + definitions `fct_zmodMixin`, `fct_ringMixin` (was only used in an `HB.instance`)
- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)
  + lemma `deg_le2_ge0` (available as `deg_le2_poly_ge0` in `ssrnum.v`
    since MathComp 2.1.0)
  + definitions `monotonous`, `boxed`, `onem`, `inv_fun`,
    `bound_side`, `swap`, `prodA`, `prodAr`, `map_pair`, `sigT_fun`
    (moved to new file `unstable.v` that shouldn't be used outside of
    Analysis)
  + notations `` `1 - r ``, `f \^-1` (moved to new file `unstable.v`
    that shouldn't be used outside of Analysis)
  + lemmas `dependent_choice_Type`, `maxr_absE`, `minr_absE`,
    `le_bigmax_seq`, `bigmax_sup_seq`, `leq_ltn_expn`, `last_filterP`,
    `path_lt_filter0`, `path_lt_filterT`, `path_lt_head`,
    `path_lt_last_filter`, `path_lt_le_last`, `sumr_le0`,
    `fset_nat_maximum`, `image_nat_maximum`, `card_fset_sum1`,
    `onem0`, `onem1`, `onemK`, `add_onemK`, `onem_gt0`, `onem_ge0`,
    `onem_le1`, `onem_lt1`, `onemX_ge0`, `onemX_lt1`, `onemD`,
    `onemMr`, `onemM`, `onemV`, `lez_abs2`, `ler_gtP`, `ler_ltP`,
    `real_ltr_distlC`, `prodAK`, `prodArK`, `swapK`, `lt_min_lt`,
    `intrD1`, `intr1D`, `floor_lt_int`, `floor_ge0`, `floor_le0`,
    `floor_lt0`, `floor_eq`, `floor_neq0`, `ceil_gt_int`, `ceil_ge0`,
    `ceil_gt0`, `ceil_le0`, `abs_ceil_ge`, `nat_int`, `bij_forall`,
    `and_prop_in`, `mem_inc_segment`, `mem_dec_segment`,
    `partition_disjoint_bigfcup`, `partition_disjoint_bigfcup`,
    `prodr_ile1`, `size_filter_gt0`, `ltr_sum`, `ltr_sum_nat` (moved
    to new file `unstable.v` that shouldn't be used outside of
    Analysis)

- in `reals.v`:
  + lemmas `floor_le`, `le_floor` (deprecated since 1.3.0)

- file `lebesgue_integral.v` (split in several files in the directory
  `lebesgue_integral_theory`)

- in `classical_sets.v`:
  + notations `setvI`, `setIv`, `bigcup_set`, `bigcup_set_cond`, `bigcap_set`,
    `bigcap_set_cond`
- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)
- in `topology_structure.v`:
  + lemma `closureC`

- in file `lebesgue_integral.v`:
  + lemma `approximation`

### Removed

- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`

- in `cardinality.v`:
  + lemma `cst_fimfun_subproof`

- in `lebesgue_integral.v`:
  + lemma `cst_mfun_subproof` (use lemma `measurable_cst` instead)
  + lemma `cst_nnfun_subproof` (turned into a `Let`)
  + lemma `indic_mfun_subproof` (use lemma `measurable_fun_indic` instead)

- in `lebesgue_integral.v`:
  + lemma `measurable_indic` (was uselessly specializing `measurable_fun_indic` (now `measurable_indic`) from `lebesgue_measure.v`)
  + notation `measurable_fun_indic` (deprecation since 0.6.3)
- in `constructive_ereal.v`
  + notation `lee_opp` (deprecated since 0.6.5)
  + notation `lte_opp` (deprecated since 0.6.5)
- in `measure.v`:
  + `dynkin_setI_bigsetI` (use `big_ind` instead)

- in `lebesgue_measurable.v`:
  + notation `measurable_fun_power_pos` (deprecated since 0.6.3)
  + notation `measurable_power_pos` (deprecated since 0.6.4)

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`

- in `measurable_realfun.v`:
  + notation `measurable_fun_ln` (deprecated since 0.6.3)
  + notations `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd` (deprecated since 0.6.2)
  + notation `measurable_fun_lim_sup` (deprecated since 0.6.6)
  + notation `measurable_fun_max` (deprecated since 0.6.3)
  + notation `measurable_fun_er_map` (deprecated since 0.6.3)
  + notations `emeasurable_funN`, `emeasurable_fun_max`, `emeasurable_fun_min`,
    `emeasurable_fun_funepos`, `emeasurable_fun_funeneg` (deprecated since 0.6.3)
  + notation `measurable_fun_lim_esup` (deprecated since 0.6.6)

- in `measure.v`:
  + notation `measurable_fun_ext` (deprecated since 0.6.2)
  + notations `measurable_fun_id`, `measurable_fun_cst`, `measurable_fun_comp` (deprecated since 0.6.3)
  + notation `measurable_funT_comp` (deprecated since 0.6.3)

- in `hoelder.v`:
  + lemma `oppr_Lnorm`

### Infrastructure

### Misc
