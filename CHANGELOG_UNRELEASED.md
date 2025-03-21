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

- in `lebesgue_integral_approximation.v`:
  + lemma `measurable_prod`

### Changed

- in `pi_irrational`:
  + definition `rational`

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
  + lemma `image_nonempty`

- in `mathcomp_extra.v`:
  + lemmas `eq_exists2l`, `eq_exists2r`

- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`

- in `charge.v`:
  + lemma `ae_eq_mul2l`

- in `hoelder.v`
  + lemmas `Lnorm0`, `oppr_Lnorm`, `Lnorm_cst1`
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

- in `lebesgue_integral.v`:
  + lemma `mfunMn`

- in `classical_sets.v`:
  + lemma `set_cst`

- in `measurable_realfun.v`:
  + lemmas `ereal_inf_seq`, `ereal_sup_seq`,
    `ereal_sup_cst`, `ereal_inf_cst`, `ereal_sup_pZl`,
    `ereal_supZl`, `ereal_inf_pZl`, `ereal_infZl`

- in `measure.v`:
  + lemmas `seqDU_measurable`, `measure_gt0`
  + notation `\forall x \ae mu , P`
  + notations `f = g %[ae mu in D ]`, `f = g %[ae mu ]`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`
  + instances `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
  + lemmas `ae_eq_comp2`, `ae_foralln`

- in `functions.v`:
  + lemma `natmulfctE`

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

### Changed

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package
- moved from `gauss_integral` to `trigo.v`:
  + `oneDsqr`, `oneDsqr_ge1`, `oneDsqr_inum`, `oneDsqrV_le1`,
    `continuous_oneDsqr`, `continuous_oneDsqr`
- moved, generalized, and renamed from `gauss_integral` to `trigo.v`:
  + `integral01_oneDsqr` -> `integral0_oneDsqr`

- in `interval_inference.v`:
  + definition `IntItv.exprn_le1_bound`
  + lemmas `Instances.nat_spec_succ`, `Instances.num_spec_natmul`,
    `Instances.num_spec_intmul`, `Instances.num_itv_bound_exprn_le1`
  + canonical instance `Instances.succn_inum`

- in `lebesgue_integral_properties.v`
  (new file with contents moved from `lebesgue_integral.v`)
  + `le_normr_integral` renamed to `le_normr_Rintegral`

- moved to `lebesgue_measure.v` (from old `lebesgue_integral.v`)
  + `compact_finite_measure`

- moved from `ftc.v` to `lebesgue_integral_under.v` (new file)
  + notation `'d1`, definition `partial1of2`, lemmas `partial1of2E`,
    `cvg_differentiation_under_integral`, `differentiation_under_integral`,
    `derivable_under_integral`
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

- in `lebesgue_integral.v`:
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`
  + `measurable_funP` -> `measurable_funPT` (field of `isMeasurableFun` mixin)

- in `mathcomp_extra.v`
  + `comparable_min_le_min` -> `comparable_le_min2`
  + `comparable_max_le_max` -> `comparable_le_max2`
  + `min_le_min` -> `le_min2`
  + `max_le_max` -> `le_max2`
  + `real_sqrtC` -> `sqrtC_real`

- in `boolp.v`:
  + `eq_fun2` -> `eq2_fun`
  + `eq_fun3` -> `eq3_fun`
  + `eq_forall2` -> `eq2_forall`
  + `eq_forall3` -> `eq3_forall`
- in `ereal.v`:
  + `ereal_sup_le` -> `ereal_sup_ge`

- in `hoelder.v`:
  + `minkowski` -> `minkowski_EFin`
  + `Lnorm_ge0` -> `Lnormr_ge0`
  + `Lnorm_eq0_eq0` -> `Lnormr_eq0_eq0`

### Generalized

- in `constructive_ereal.v`:
  + lemma `EFin_natmul`

- in `lebesgue_integral.v`
  + lemmas `measurable_funP`, `ge0_integral_pushforward`,
    `integrable_pushforward`, `integral_pushforward`

- in `real_interval.v`:
  + lemmas `bigcup_itvT`, `itv_bndy_bigcup_BRight`, `itv_bndy_bigcup_BLeft_shift`
- in `hoelder.v`:
  + definition `Lnorm` generalized to functions with codomain `\bar R`
    (this impacts the notation `'N_p[f]`)
  + lemmas `Lnorm1`, `eq_Lnorm` (from `f : _ -> R` to `f : _ -> \bar R`)

- in `probability.v`
  + lemma `cantelli`

### Deprecated

### Removed

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

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`

### Infrastructure

### Misc
