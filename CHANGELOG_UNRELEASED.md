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
  + lemma `LType1_integrable`, `LType2_integrable_sqr`
  + definitions `finlfun`, `lfun`, `lfun_key`
  + canonical `lfun_keyed`
  + lemmas `sub_lfun_mfun`, `sub_lfun_finlfun`
  + definition `lfun_Sub`
  + lemmas `lfun_rect`, `lfun_valP`, `lfuneqP`, `lfuny0`, `mfunP`, `lfunP`,
    `mfun_scaler_closed`
  + lemmas `LnormZ`, `lfun_submod_closed`
  + lemmas `finite_norm_fine`, `ler_LnormD`,
    `LnormN`, `Lnorm_natmul`, `fine_Lnorm_eq0`
  + lemma `Lspace_inclusion`

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

### Renamed

- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`

- in `lebesgue_integral_approximation.v`:
  + `emeasurable_fun_lt` -> `measurable_lte`
  + `emeasurable_fun_le` -> `measurable_lee`
  + `emeasurable_fun_eq` -> `measurable_lee`
  + `emeasurable_fun_neq` -> `measurable_neqe`

- file `lebesgue_integral_approximation.v` -> `measurable_fun_approximation.v`

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
- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`
- in `boolp.v`:
  + `eq_fun2` -> `eq2_fun`
  + `eq_fun3` -> `eq3_fun`
  + `eq_forall2` -> `eq2_forall`
  + `eq_forall3` -> `eq3_forall`
- in `ereal.v`:
  + `ereal_sup_le` -> `ereal_sup_ge`

- in `hoelder.v`:
  + `minkowski` -> `minkowski_EFin`

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

### Deprecated

### Removed

- in `functions.v`:
  + definitions `fct_ringMixin`, `fct_ringMixin` (was only used in an `HB.instance`)
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

### Infrastructure

### Misc
