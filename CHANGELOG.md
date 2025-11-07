# Changelog

Latest releases: [[1.14.0] - 2025-11-07](#1140---2025-11-07), [[1.13.0] - 2025-08-16](#1130---2025-08-16), and [[1.12.0] - 2025-07-03](#1120---2025-07-03)

## [1.14.0] - 2025-11-07

### Added

- in `unstable.v`:
  + lemmas `coprime_prodr`, `Gauss_dvd_prod`, `expn_prod`, `mono_leq_infl`,
    `card_big_setU`
  + lemmas `leq_Mprod_prodD`, `leq_fact2`, `normr_onem`

- in `set_interval.v`:
  + lemmas `itv_setU_setT`, `disjoint_rays`

- in `constructive_ereal.v`:
  + lemma `ltgte_fin_num`
  + lemmas `mule_natr`, `dmule_natr`
  + lemmas `inve_eqy`, `inve_eqNy`
  + variants `Ione`, `Idummy_placeholder`
  + inductives `Inatmul`, `IEFin`
  + definition `parse`, `print`
  + number notations in scopes `ereal_dual_scope` and `ereal_scope`
  + notation `- 1` in scopes `ereal_dual_scope` and `ereal_scope`
  + lemma `lt0_adde`

- in `uniform_structure.v`:
  + lemma `continuous_injective_withinNx`

- in `function_spaces.v`:
  + lemmas `cvg_big`, `continuous_big`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `le0_ball0`
  + lemma `continuous_comp_cvg`

- in `num_normedtype.v`:
  + lemma `nbhs_infty_gtr`
  + lemmas `bigcup_ointsub_sup`, `bigcup_ointsub_mem`

- in `normed_module.v`:
  + lemma `bigcup_ointsubxx`, `nondisjoint_bigcup_ointsub`
  + definition `open_disjoint_itv`
  + lemmas `open_disjoint_itv_open`, `open_disjoint_itv_is_interval`,
    `open_disjoint_itv_trivIset`, `open_disjoint_itv_bigcup`

- in `landau.v`:
  + lemma `littleoE0`

- in `realfun.v`:
  + lemma `cvg_addrl_Ny`
  + lemmas `derivable_oy_continuous_within_itvcy`,
           `derivable_oy_continuous_within_itvNyc`
  + lemmas `derivable_oo_continuousW`,
           `derivable_oy_continuousWoo`,
           `derivable_oy_continuousW`,
           `derivable_Nyo_continuousWoo`,
           `derivable_Nyo_continuousW`

- in `derive.v`:
  + lemma `derive1_onem`

- in `exp.v`:
  + lemma `ln_eq0`

- in `ftc.v`:
  + lemmas `integration_by_substitution_onem`, `Rintegration_by_substitution_onem`

- in `probability.v`:
  + definition `ccdf`
  + lemmas `lebesgue_stieltjes_cdf_id`, `cdf_ccdf_1`, `ccdf_nonincreasing`,
    `cvg_ccdfy0`, `cvg_ccdfNy1`, `ccdf_right_continuous`, `ge0_expectation_ccdf`
  + corollaries `ccdf_cdf_1`, `ccdf_1_cdf`, `cdf_1_ccdf`
  + lemmas `continuous_onemXn`, `onemXn_derivable`,
    `derivable_oo_continuous_bnd_onemXnMr`, `derive_onemXn`,
    `Rintegral_onemXn`
  + definition `XMonemX`
  + lemmas `XMonemX_ge0`, `XMonemX_le1`, `XMonemX0n`, `XMonemXn0`,
    `XMonemX00`, `XMonemXC`, `XMonemXM`
  + lemmas `continuous_XMonemX`, `within_continuous_XMonemX`,
    `measurable_XMonemX`, `bounded_XMonemX`, `integrable_XMonemX`,
    `integrable_XMonemX_restrict`, `integral_XMonemX_restrict`
  + definition `beta_fun`
  + lemmas `EFin_beta_fun`, `beta_fun_sym`, `beta_fun0n`, `beta_fun00`,
    `beta_fun1Sn`, `beta_fun11`, `beta_funSSnSm`, `beta_funSnSm`, `beta_fun_fact`
  + lemmas `beta_funE`, `beta_fun_gt0`, `beta_fun_ge0`
  + definition `beta_pdf`
  + lemmas `measurable_beta_pdf`, `beta_pdf_ge0`, `beta_pdf_le_beta_funV`,
    `integrable_beta_pdf`, `bounded_beta_pdf_01`
  + definition `beta_prob`
  + lemmas `integral_beta_pdf`, `beta_prob01`, `beta_prob_fin_num`,
    `beta_prob_dom`, `beta_prob_uniform`,
    `integral_beta_prob_bernoulli_prob_lty`,
    `integral_beta_prob_bernoulli_prob_onemX_lty`,
    `integral_beta_prob_bernoulli_prob_onem_lty`, `beta_prob_integrable`,
    `beta_prob_integrable_onem`, `beta_prob_integrable_dirac`,
    `beta_prob_integrable_onem_dirac`, `integral_beta_prob`
  + definition `div_beta_fun`
  + lemmas `div_beta_fun_ge0`, `div_beta_fun_le1`
  + definition `beta_prob_bernoulli_prob`
  + lemma `beta_prob_bernoulli_probE`

- new file `pnt.v`
  + definitions `next_prime`, `prime_seq`
  + lemmas `leq_prime_seq`, `mem_prime_seq`
  + theorem `dvg_sum_inv_prime_seq`

- new directory `theories/measure_theory` with new files:
  + `measurable_structure.v`
  + `measure_function.v`
  + `counting_measure.v`
  + `dirac_measure.v`
  + `probability_measure.v`
  + `measure_negligible.v`
  + `measure_extension.v`
  + `measurable_function.v`
  + `measure.v`

### Changed

- in `constructive_ereal.v`:
  + instance of `Monoid.isLaw` for `mine`

- in `matrix_topology.v`:
  + definition `mx_ball`

- moved from `vitali_lemma.v` to `pseudometric_normed_Zmodule.v` and renamed:
  + `closure_ball` -> `closure_ballE`

- moved from `theories/measure.v` (now removed)
  + to `sequences.v`:
    * lemmas `epsilon_trick`, `epsilon_trick0`
  + to `measure_theory/measurable_structure.v`:
    * definitions `setC_closed`, `setI_closed`, `setU_closed`, `setSD_closed`,
      `setD_closed`, `setY_closed`, `fin_bigcap_closed`, `finN0_bigcap_closed`,
      `fin_bigcup_closed`, `semi_setD_closed`
    * lemma `setD_semi_setD_closed`
    * definitions `ndseq_closed`, `niseq_closed`, `trivIset_closed`, `fin_trivIset_closed`,
      `setring`, `sigma_ring`, `sigma_algebra`, `dynkin`, `lambda_system`,
      `monotone`
    * lemmas `powerset_sigma_ring`, `powerset_lambda_system`
    * notations `<<l _, >>`, `<<l _ >>`, `<<d _ >>`, `<<s _, _>>`, `<<s _ >>`,
      `<<r _ >>`, `<<sr _ >>`, `<<M _ >>`
    * lemmas `lambda_system_smallest`, `fin_bigcup_closedP`, `finN0_bigcap_closedP`,
      `setD_closedP`, `sigma_algebra_bigcap`, `sigma_algebraP`, `smallest_sigma_algebra`,
      `sub_sigma_algebra2`, `sigma_algebra_id`, `sub_sigma_algebra`,
      `sigma_algebra0`, `sigma_algebraCD`, `sigma_algebra_bigcup`,
      `smallest_setring`, `sub_setring2`, `setring_id`, `sub_setring`,
      `setring0`, `setringD`, `setringU`, `setring_fin_bigcup`, `g_sigma_algebra_lambda_system`,
      `smallest_sigma_ring`, `sigma_ring_monotone`, `g_sigma_ring_monotone`,
      `sub_g_sigma_ring`, `setring_monotone_sigma_ring`, `g_monotone_monotone`,
      `g_monotone_setring`, `g_monotone_g_sigma_ring`, `monotone_setring_sub_g_sigma_ring`,
      `smallest_lambda_system`, `lambda_system_subset`, `dynkinT`, `dynkinC`,
      `dynkinU`, `dynkin_lambda_system`, `g_dynkin_dynkin`, `sigma_algebra_dynkin`,
      `dynkin_setI_sigma_algebra`, `setI_closed_g_dynkin_g_sigma_algebra`
    * definition `strace`
    * lemmas `subset_strace`, `g_sigma_ring_strace`, `strace_sigma_ring`,
      `setI_g_sigma_ring`, `sigma_algebra_strace`
    * mixin `isSemiRingOfSets`, structure `SemiRingOfSets`,
      notation `semiRingOfSetsType`
    * lemma `measurable_curry`
    * notations `.-measurable`, `'measurable`
    * mixin `SemiRingOfSets_isRingOfSets`, structure `RingOfSets`,
      notation `ringOfSetsType`
    * mixin `RingOfSets_isAlgebraOfSets`, structure `AlgebraOfSets`,
      notation `algebraOfSetsType`
    * mixin `hasMeasurableCountableUnion`
    * structure `SigmaRing`, structure `SigmaRing`, notation `sigmaRingType`
    * factory `isSigmaRing`
    * structure `Measurable`, notation `measurableType`
    * factories `isRingOfSets`, `isRingOfSets_setY`, `isAlgebraOfSets`,
      `isAlgebraOfSets_setD`, `isMeasurable`
    * lemmas `bigsetU_measurable`, `fin_bigcup_measurable`, `measurableD`,
      `seqDU_measurable`, ` measurableC`, `bigsetI_measurable`, `fin_bigcap_measurable`,
      `measurableID`, `bigcup_measurable`, `bigcap_measurable`, `bigcapT_measurable`,
      `countable_measurable`, `sigmaRingType_lambda_system`, `countable_bigcupT_measurable`,
      `bigcupT_measurable_rat`, `sigma_algebra_measurable`, `bigcap_measurableType`
    * definition `discrete_measurable`
    * lemmas `discrete_measurable0`, `discrete_measurableC`, `discrete_measurableU`
    * definitions `sigma_display`, `g_sigma_algebraType`
    * lemmas `sigma_algebraC`
    * notations `.-sigma`, `.-sigma.-measurable`
    * lemma `measurable_g_measurableTypeE`
    * definition `preimage_set_system`
    * lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
      `preimage_set_system_id`, `sigma_algebra_preimage`
    * definition `image_set_system`
    * lemmas `sigma_algebra_image`, `g_sigma_preimageE`
    * definition `subset_sigma_subadditive`
    * lemmas `big_trivIset`
    * definition `covered_by`
    * lemmas `covered_bySr`, `covered_byP`, `covered_by_finite`, `covered_by_countable`,
      `measurable_uncurry`
    * definition `g_sigma_preimageU`
    * lemmas `g_sigma_preimageU_comp`
    * definition `measure_prod_display`
    * notation `.-prod`, `.-prod.-measurable`
    * lemmas `measurableX`, `measurable_prod_measurableType`,
      `measurable_prod_g_measurableTypeR`, `measurable_prod_g_measurableType`
    * definition `g_sigma_preimage`
    * lemma `g_sigma_preimage_comp`
    * definition `measure_tuple_display`
    * definition `measure_dominates`, notation ``` `<< ```
    * lemma `measure_dominates_trans`
  + to `measure_theory/measure_function.v`:
    * definitions `semi_additive2`, `semi_additive`, `semi_sigma_additive`,
      `additive2`, `additive`, `sigma_additive`, `subadditive`,
      `measurable_subset_sigma_subadditive`
    * lemma `semi_additiveW`
    * lemmas `semi_additiveE`, `semi_additive2E`, `additive2P`
    * lemmas `semi_sigma_additive_is_additive`, `semi_sigma_additiveE`,
      `sigma_additive_is_additive`
    * mixin `isContent`, structure `Content`, notation `{content set _ -> \bar _}`
    * lemma `content_inum_subproof`
    * lemmas `measure0`, `measure_gt0`, `measure_semi_additive_ord`,
      `measure_semi_additive_ord_I`, `content_fin_bigcup`, `measure_semi_additive2`
    * lemmas `measureU`, `measure_bigsetU`, `measure_fin_bigcup`,
      `measure_bigsetU_ord_cond`, `measure_bigsetU_ord`, `measure_fbigsetU`
    * mixin `Content_isMeasure`
    * structure `Measure`, notations `measure`,
      `{measure set _ -> \bar _}`
    * lemma `measure_inum_subproof`
    * factory `isMeasure`, lemma `eq_measure`
    * lemmma `measure_semi_bigcup`
    * lemmas `measure_sigma_additive`, `measure_bigcup`
    * definition `msum`
    * definition `mzero`, lemma `msum_mzero`
    * definition `measure_add`, `measure_addE`
    * definition `mscale`
    * definition `mseries`
    * definition `pushforward`
    * module `SetRing`
    * notations `.-ring`, `.-ring.-measurable`
    * lemmas `le_measure`, `measure_le0`
    * lemmas `content_subadditive`, `content_sub_fsum`
    * lemmas `content_ring_sup_sigma_additive`, `content_ring_sigma_additive`
    * lemmas `ring_sigma_subadditive`, `ring_semi_sigma_additive`,
      `semiring_sigma_additive`
    * factory `Content_SigmaSubAdditive_isMeasure`
    * lemma `measure_sigma_subadditive`
    * lemma `measure_sigma_subadditive_tail`
    * definition `fin_num_fun`
    * lemmas `fin_num_fun_lty`, `lty_fin_num_fun`
    * definitions `sfinite_measure`, `sigma_finite`
    * lemma `fin_num_fun_sigma_finite`
    * definition `mrestr`
    * lemma `sfinite_measure_sigma_finite`
    * mixin `isSFinite`, structure `SFiniteMeasure`,
      notation `{sfinite_measure set _ -> \bar _}`
    * mixin `isSigmaFinite`, structure `SigmaFiniteContent`,
      notation `sigma_finite_content`, `{sigma_finite_content set _ -> \bar _}`
    * structure `SigmaFiniteMeasure`, notations `sigma_finite_measure`,
      `{sigma_finite_measure set _ -> \bar _}`
    * factory `Measure_isSigmaFinite`
    * lemmas `sigma_finite_mzero`, `sfinite_mzero`
    * mixin `isFinite`, structures `FinNumFun`, `FiniteMeasure`,
      notation `{finite_measure set _ -> \bar _}`
    * factories `Measure_isFinite`, `Measure_isSFinite`
    * definition `sfinite_measure_seq`
    * lemma `sfinite_measure_seqP`
    * definition `mfrestr`
    * lemmas `measureIl`, `measureIr`, `subset_measure0`
    * lemmas `measureDI`, `measureD`, `measureU2`
    * lemmas `measureUfinr`, `measureUfinl`, `null_set_setU`, `measureU0`
    * lemma `eq_measureU`
    * lemma `g_sigma_algebra_measure_unique_trace`
    * lemmas `nondecreasing_cvg_mu`, `nonincreasing_cvg_mu`
    * definition `lim_sup_set`
    * lemmas `lim_sup_set_ub`, `lim_sup_set_cvg`
    * lemma `lim_sup_set_cvg0`
    * theorem `Boole_inequality`
    * lemma `sigma_finiteP`
    * theorem `generalized_Boole_inequality`
    * lemmas `g_sigma_algebra_measure_unique_cover`, `g_sigma_algebra_measure_unique`
    * lemma `measure_unique`
  + to `measure_theory/counting_measure.v`:
    * definition `counting`
    * lemma `sigma_finite_counting`
  + to `measure_theory/dirac_measure.v`:
    * definition `dirac`, notation `\d_`
    * lemmas `finite_card_sum`, `finite_card_dirac`, `infinite_card_dirac `
  + to `measure_theory/probability_measure.v`:
    * mixin `isSubProbability`, structure `SubProbability`, notation `subprobability`
    * factory `Measure_isSubProbability`
    * mixin `isProbability`, structure `Probability`, notation `probability`
    * lemmas `probability_le1`, `probability_setC`
    * factory `Measure_isProbability`
    * definition `mnormalize`
    * lemmas `mnormalize_id`
    * definitions `mset`, `pset`, `pprobability`
    * lemmas `lt0_mset`, `gt1_mset`
  + to `measure_theory/measure_negligible.v`:
    * definition `negligible`, notation `.-negligible`
    * lemmas `negligibleP`, `negligible_set0`, `measure_negligible`, `negligibleS`,
      `negligibleI`
    * definition `measure_is_complete`
    * lemmas `negligibleU`, `negligible_bigsetU`, `negligible_bigcup`
    * definition `almost_everywhere`, `ae_filter_ringOfSetsType`,
      `ae_properfilter_algebraOfSetsType`
    * definition `ae_eq`, notations `{ae _, _}`, `\forall _ \ae _, _`,
      `_ = _ [%ae _ in _]`, `_ = _ %[ae _]`
    * lemmas `measure0_ae`, `aeW`
    * instance `ae_eq_equiv`
    * instances `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
    * lemmas `ae_eq0`, `ae_eq_refl`, `ae_eq_comp`, `ae_eq_comp2`,
      `ae_eq_funeposneg`, `ae_eq_sym`, `ae_eq_trans`, `ae_eq_sub`,
      `ae_eq_mul2r`, `ae_eq_mul2l`, `ae_eq_mul1l`, `ae_eq_abse`, `ae_foralln`
    * lemmas `ae_eq_subset`, `ae_eqe_mul2l`
    * lemma `measure_dominates_ae_eq`
  + to `measure_theory/measure_extension.v`:
    * definitions `sigma_subadditive`, `subset_sigma_subadditive`
    * mixin `isOuterMeasure`, structure `OuterMeasure`
    * notation `{outer_measure set _ -> \bar _}`
    * factory `isSubsetOuterMeasure`
    * lemmas `outer_measure_sigma_subadditive_tail`, `outer_measure_subadditive`,
      `outer_measureU2`, `le_outer_measureIC`
    * definition `caratheodory_measurable`, notation `.-caratheodory`
    * lemma `le_caratheodory_measurable`
    * lemmas `outer_measure_bigcup_lim`, `caratheodory_measurable_set0`,
      `caratheodory_measurable_setC`, `caratheodory_measurable_setU_le`,
      `caratheodory_measurable_setU`, `caratheodory_measurable_bigsetU`,
      `caratheodory_measurable_setI`, `caratheodory_measurable_setD`,
      `disjoint_caratheodoryIU`, `caratheodory_additive`, `caratheodory_lime_le`,
      `caratheodory_measurable_trivIset_bigcup`, `caratheodory_measurable_bigcup`
    * definition `caratheodory_type`, notation `.-cara.-measurable`
    * definition `caratheodory_display`, notation `.-cara`
    * lemmas `caratheodory_measure0`, `caratheodory_measure_ge0`,
      `caratheodory_measure_sigma_additive`, `measure_is_complete_caratheodory`
    * definition `measurable_cover`, lemmas `cover_measurable`, `cover_subset`
    * definition `mu_ext`, notation `^*`
    * lemmas `le_mu_ext`, `mu_ext_ge0`, `mu_ext0`, `mu_ext_sigma_subadditive`
    * lemmas `Rmu_ext`, `measurable_mu_extE`, `measurable_Rmu_extE`
    * lemma `sub_caratheodory`
    * definition `measure_extension`
    * lemmas `measure_extension_sigma_finite`, `measure_extension_unique`
    * lemma `caratheodory_measurable_mu_ext`
    * definition `completed_measure_extension`
    * lemma `completed_measure_extension_sigma_finite`
  + to `measure_theory/measurable_function.v`:
    * mixin `isMeasurableFun`, structure `MeasurableFun`, notations `{mfun _ >-> _}`,
      `[mfun of _]`
    * lemmas `measurable_funP`, `measurable_funPTI`
    * definitions `mfun`, `mfun_key`, canonical `mfun_keyed`
    * lemmas `measurable_id`, `measurable_comp`, `eq_measurable_fun`,
      `measurable_fun_eqP`, `measurable_cst`, `measurable_fun_bigcup`,
      `measurable_funU`, `measurable_funS`, `measurable_fun_if`,
      `measurable_fun_set0`, `measurable_fun_set1`
    * definitions `mfun_Sub_subproof`, `mfun_Sub`
    * lemmas `mfun_rect`, `mfun_val`, `mfuneqP`
    * lemmas `measurableT_comp`, `measurable_funTS`, `measurable_restrict`,
      `measurable_restrictT`, `measurable_fun_ifT`, `measurable_fun_bool`,
      `measurable_and`, `measurable_neg`, `measurable_or`
    * lemmas `preimage_set_system_measurable_fun`, `measurability`
    * lemmas `measurable_fun_pairP`, `measurable_fun_pair`
    * lemmas `measurable_fst`, `measurable_snd`, `measurable_swap`
    * lemmas `measurable_tnth`, `measurable_fun_tnthP`, `measurable_cons`
    * lemmas `measurable_behead`, `measurable_fun_if_pair`
    * lemmas `pair1_measurable`, `pair2_measurable`
    * lemmas `measurable_xsection`, `measurable_ysection`,
      `measurable_fun_pair1`, `measurable_fun_pair2`

- in `lebesgue_stieltjes_measure.v` specialized from `numFieldType` to `realFieldType`:
  + lemma `nondecreasing_right_continuousP`
  + definition `CumulativeBounded`

- in `lebesgue_stieltjes_measure.v`, according to generalization of `Cumulative`, modified:
  + lemmas `wlength_ge0`, `cumulative_content_sub_fsum`, `wlength_sigma_subadditive`, `lebesgue_stieltjes_measure_unique`
  + definitions `lebesgue_stieltjes_measure`, `completed_lebesgue_stieltjes_measure`

- in `probability.v`:
  + definition `poisson_pmf`, lemmas `poisson_pmf_ge0`, `measurable_poisson_pmf`,
  + definition `poisson_prob`

### Renamed

- in `reals.v`:
  + `sup_le_ub` -> `ge_sub`
  + `le_inf` -> `inf_le`
  + `le_sup` -> `sup_le`
  + `sup_ubound` -> `ub_le_sup`
  + `inf_lbound` -> `ge_inf`
  + `ub_ereal_sup` -> `ge_ereal_sup`
  + `ereal_inf_le` -> `ge_ereal_inf`
  + `le_ereal_sup` -> `ereal_sup_le`
  + `le_ereal_inf` -> `ereal_inf_le_tmp`
  + `lb_ereal_inf` -> `le_ereal_inf_tmp`
  + `ereal_sup_ge` -> `le_ereal_sup_tmp`

- in `sequences.v`:
  + `adjacent` -> `adjacent_seq`

- in `realfun.v`:
  + `derivable_oo_continuous_bnd` -> `derivable_oo_LRcontinuous`
  + `derivable_oo_continuous_bnd_within` -> `derivable_oo_LRcontinuous_within`
  + `derivable_Nyo_continuous_bnd` -> `derivable_Nyo_Lcontinuous`
  + `derivable_oy_continuous_bnd` -> `derivable_oy_Rcontinuous`
  + `derivable_oy_continuous_within_itvcy` -> `derivable_oy_Rcontinuous_within_itvcy`

- in `probability.v`:
  + `bernoulli` -> `bernoulli_prob`
  + `bernoulli_probE` -> `bernoulliE`
  + `integral_bernoulli_prob` -> `integral_bernoulli_prob`
  + `measurable_bernoulli` -> `measurable_bernoulli_prob`
  + `measurable_bernoulli2` -> `measurable_bernoulli_prob2`

### Generalized

- in `unstable.v`:
  + generalized from `numDomainType` to `pzRingType`:
    + definition `onem`, lemmas `onme0`, `onem1`, `add_onemK`, `onemD`, `onemMr`, `onemM`

- in `set_interval.v`:
  + lemma `set_itv_splitI` (generalized from `orderType` to `porderType`)
  + lemma `disjoint_itvxx` (generalized from `numDomainType` to `porderType`)
  + lemma `disjoint_neitv` (generalized from `realFieldType` to `orderType`)

- in `pseudometric_normed_Zmodule.v`:
  + lemma `closed_ball0` (`realFieldType` -> `pseudoMetricNormedZmodType`)
  + lemmas `closed_ball_closed`, `subset_closed_ball` (`realFieldType` -> `numDomainType`)
  + lemma `subset_closure_half` (`realFieldType` -> `numFieldType`)
  + lemma `le_closed_ball` (`pseudoMetricNormedZmodType` -> `pseudoMetricType`)

- in `matrix_normedtype.v`:
  + lemmas `rV_compact`, `mx_norm_ball`, `bounded_closed_compact`,
    `mx_normZ`
  + example `matrix_triangle`

- in `lebesgue_stieltjes_measure.v` generalized (codomain is now an `orderNbhsType`):
  + lemma `right_continuousW`
  + record `isCumulative`
  + definition `Cumulative`

- in `probabilitity.v`:
  + lemma `exponential_pdf_ge0` (hypothesis generalized)

### Removed

- file `interval_inference.v` (now in MathComp)

- in `reals.v`:
  + notation `sup_ub` (was deprecated since 1.3.0)
  + notation `inf_lb` (was deprecated since 1.3.0)
  + notation `ereal_sup_ub` (was deprecated since 1.3.0)
  + notation `ereal_inf_lb` (was deprecated since 1.3.0)

- in file `all_reals.v`
  + export of `interval_inference` (now in mathcomp-algebra, but not automatically exported)

- in `ereal.v`:
  + notation `ereal_sup_le` (was deprecated since 1.11.0)

- file `theories/measure.v`
  + notations `[measure of _]`, `[measure of _]`
  + notations `[content of _]`, `[content of _]`
  + notations `[outer_measure of _]`, `[outer_measure of _]`

## [1.13.0] - 2025-08-16

### Added

- in `unstable.v`:
  + lemma `sqrtK`

- in `mathcomp_extra.v`:
  + lemmas `subrKC`, `sumr_le0`, `card_fset_sum1`

- in `functions.v`:
  + lemmas `fct_prodE`, `prodrfctE`

- in `classical_orders.v`:
  + lemma `big_lexi_order_prefix_closed_itv`

- in `topology_structure.v`:
  + lemmas `denseI`, `dense0`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `dense_set1C`

- in `constructive_ereal.v`:
  + lemma `expe0`, `mule0n`, `muleS`

- in `reals.v`:
  + definition `irrational`
  + lemmas `irrationalE`, `rationalP`

- new file `borel_hierarchy.v`:
  + definitions `Gdelta`, `Fsigma`
  + lemmas `closed_Fsigma`, `Gdelta_measurable`, `Gdelta_subspace_open`,
    `irrational_Gdelta`, `not_rational_Gdelta`

- in `realfun.v`:
  + instance `is_derive1_sqrt`

- in `exp.v`:
  + lemma `norm_expR`
  + lemmas `expeR_eqy`
  + lemmas `lt0_powR1`, `powR_eq1`
  + definition `lne`
  + lemmas `le0_lneNy`, `lne_EFin`, `expeRK`, `lneK`, `lneK_eq`, `lne1`, `lneM`,
    `lne_inj`, `lneV`, `lne_div`, `lte_lne`, `lee_lne`, `lneXn`, `le_lne1Dx`,
    `lne_sublinear`, `lne_ge0`, `lne_lt0`, `lne_gt0`, `lne_le0`
  + lemma `lne_eq0`

- in `lebesgue_measure.v`:
  + lemma `countable_lebesgue_measure0`

- in `charge.v`:
  + definition `copp`, lemma `cscaleN1`

- in `hoelder.v`
  + lemma `hoelder_conj_ge1`

### Changed

- in `constructive_ereal.v`:
  + lemma `mulN1e`

- moved from `pi_irrational.v` to `reals.v` and changed
  + definition `rational`

- in `measurable_realfun.v`:
  + generalized and renamed:
    * `measurable_fun_itv_bndo_bndc` -> `measurable_fun_itv_bndo_bndcP`
    * `measurable_fun_itv_obnd_cbnd` -> `measurable_fun_itv_obnd_cbndP`

- moved from `simple_functions.v` to `measure.v`
  + notations `{mfun _ >-> _}`, `[mfun of _]`
  + mixin `isMeasurableFun`, structure `MesurableFun`, lemmas `measurable_funP`
  + definitions `mfun`, `mfun_key`, canonical `mfun_keyed`
  + definitions `mfun_Sub_subproof`, `mfun_Sub`
  + lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`
  + lemma `measurableT_comp_subproof`

- moved from `simple_functions.v` to `measure.v` and renamed:
  + lemma `measurable_sfunP` -> `measurable_funPTI`

- moved from `simple_functions.v` to `measurable_realfun.v`
  + lemmas `mfun_subring_closed`, `mfun0`, `mfun1`, `mfunN`,
    `mfunD`, `mfunB`, `mfunM`, `mfunMn`, `mfun_sum`, `mfun_prod`, `mfunX`
  + definitions `mindic`, `indic_mfun`, `scale_mfun`, `max_mfun`
  + lemmas `mindicE`, `max_mfun_subproof`

- moved from `simple_functions.v` to `lebesgue_stieltjes_measure.v` and renamed:
  + lemma `measurable_sfun_inP` -> `measurable_funP1`

### Renamed

- in `derive.v`:
  + `derivemxE` -> `deriveEjacobian`

- in `exp.v`:
  + `ltr_expeR` -> `lte_expeR`
  + `ler_expeR` -> `lee_expeR`

- in `lebesgue_stieltjes_measure.v`:
  + `cumulativeNy0` -> `cumulativeNy`
  + `cumulativey1` -> `cumulativey`

- `measurable_sfunP` -> `measurable_funPTI`
  (and moved from from `simple_functions.v` to `measure.v`)

- `measurable_sfun_inP` -> `measurable_funP1`
  (and moved from `simple_functions.v` to `lebesgue_stieltjes_measure.v`)

### Generalized

- in `functions.v`
  + lemma `fct_sumE` (from a pointwise equality to a functional one)

### Removed

- file `forms.v` (superseded by MathComp's `sesquilinear.v`)

- in `unstable.v`:
  + `dependent_choice_Type` (use Rocq's `dependent_choice` instead)

- in `simple_functions.v`:
  + duplicated hints about `measurable_set1`
  + lemma `measurableT_comp_subproof` turned into a `Let` (now in `measure.v`)

## [1.12.0] - 2025-07-03

### Added

- in `unstable.v`:
  + lemma `subrKC`

- in `classical_sets.v`:
  + lemma `bigcup_mkord_ord`

- in `set_interval.v`:
  + lemma `memB_itv`, `memB_itv0`

- in `constructive_ereal.v`:
  + `inve` a total involutive inversion function on `\bar R`, denoted `^-1` in
     the `ereal_scope` coinciding with `x^-1%R` when `x != 0` but such that
     `0^-1 = +oo` and `-oo^-1 = -oo`,
  + notation `x / y` in `ereal_scope` for `x / y = x * y^-1`,
  + lemmas `inver`, `inveP`, `fine_invr`, `inve0`, `inve1`, `invey`, `invey`,
    `inveNy`, `inveK`, `invr_inj`, `inveN`, `inve_eq0`, `inve_ge0`, `inve_gt0`,
    `inv_gt0P`, `inve_lt0`, `inve_le0`, `inve_le0P`,
  + predicate `inveM_def` with notation `x *^-1? y` defining a sufficient
    condition for the inverse and product to commute, with lemmas `inveMP`,
    `inveM_defE`, `inveM` and `fin_inveM_def`,
  + compatibility lemma `mule_defE` to bridge the former definition of
    `mule_def` with the new one.
  + lemma `fin_numV`
  + lemmas `mulVe`, `lee_pV2`, `lte_pV2`, `ltee_pV2`, `inve_pge`, `inve_pgt`,
    `inve_ple`, `inve_plt`, `inve_gt1`, `inve_ge1`.
  + lemmas `div1e`, `divee`, `inve_eq1`, `Nyconjugate`
  + lemmas `abse_prod`


- in `real_interval.v`:
  + lemma `itvNybndEbigcup`

- in `num_topology.v`:
  + `topologicalType` instance on `R^o` for `R : numDomainType`

- in `convex.v`:
  + definition `convex_quasi_associative`
    * implemented through a module `ConvexQuasiAssoc` containing
      `law` and helper lemmas
  + lemmas `convR_itv`, `convR_line_path`

- in `tvs.v`:
  + HB classes `TopologicalNmodule`, `TopologicalZmodule`, `TopologicalLmodule`
    `UniformNmodule`, `UniformZmodule`, `UniformLmodule`
  + notation `topologicalZmodType`
  + mixin `PreTopologicalNmodule_isTopologicalNmodule`,
    `TopologicalNmodule_isTopologicalZmodule`,
    `TopologicalZmodule_isTopologicalLmodule`,
    `PreUniformNmodule_isUniformNmodule`,
    `UniformNmodule_isUniformZmodule`,
    `PreUniformLmodule_isUniformLmodule`
  + structure `topologicalLmodule`
  + factories `PreTopologicalNmodule_isTopologicalZmodule`,
    `TopologicalNmodule_isTopologicalLmodule`,
    `PreUniformNmodule_isUniformZmodule`,
    `UniformNmodule_isUniformLmodule`
  + lemmas `sub_continuous`, `sub_unif_continuous`

- in `num_normedtype.v`:
  + lemmas `gt0_cvgMrNy`, `gt0_cvgMry`

- in `normed_module.v`:
  + definition `pseudoMetric_normed`
  + factory `Lmodule_isNormed`

- in `sequences.v`:
  + lemma `subset_seqDU`

- in `esum.v`:
  + lemma `nneseries_esumT`

- in `exp.v`:
  + lemma `expR_ge1Dxn`

- in `measure.v`:
  + definition `g_sigma_preimage`
  + lemma `g_sigma_preimage_comp`
  + definition `measure_tuple_display`
  + lemma `measurable_tnth`
  + lemma `measurable_fun_tnthP`
  + lemma `measurable_cons`
  + lemma `measurable_behead`
  + lemmas `seqDU_measurable`, `measure_gt0`
  + notations `\forall x \ae mu, P`, `f = g %[ae mu in D]`, `f = g %[ae mu]`
  + instances `ae_eq_equiv`, `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
  + lemma `ae_eq_comp2`
  + lemma `ae_foralln`
  + lemma `ae_eqe_mul2l`

- in `lebesgue_stieltjes_measure.v`:
  + mixin `isCumulativeBounded`, structure `CumulativeBounded` with type `cumulative_bounded`

- in `simple_functions.v`:
  + lemma `mfunMn`

- in `lebesgue_integral_definition.v`:
  + lemmas `le_measure_sintegral`, `ge0_le_measure_integral`

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_nondecreasing_set_nondecreasing_integral`,
           `ge0_nondecreasing_set_cvg_integral`,
           `le0_nondecreasing_set_nonincreasing_integral`,
	   `le0_nondecreasing_set_cvg_integral`
  + lemma `ge0_integral_ereal_sup` (was a `Let`)

- in `lebesgue_integrable.v`:
  + lemma `integral_sum`

- in `lebesgue_integral_fubini.v`:
  + lemmas `integral21_prod_meas2`, `integral12_prod_meas2`

- in `lebesgue_integral_differentiation.v`:
  + lemma `nicely_shrinking_fin_num`

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

- in `hoelder.v`:
  + lemmas `Lnorm_abse`, `Lfun_norm`
  + lemmas `Lnorm0`, `Lnorm_cst1`
  + definition `hoelder_conjugate`
  + lemmas `hoelder_conjugate0`, `hoelder_conjugate1`, `hoelder_conjugate2`,
    `hoelder_conjugatey`, `hoelder_conjugateK`
  + lemmas `lerB_DLnorm`, `lerB_LnormD`, `eminkowski`
  + definition `finite_norm`
  + mixin `isLfunction` with field `Lfunction_finite`
  + structure `Lfunction`
  + notation `LfunType`
  + notation `{mfun_ mu , U >-> V }`
  + definition `ae_eq_op`
  + lemmas `ae_eq_op_refl`, `ae_eq_op_sym`, `ae_eq_op_trans`, `aeEqMfun`
  + canonical `ae_eq_op_canonical`
  + definition `LspaceType`
  + lemma `ae_eqP`
  + definition/coercion `aqEqMfun_to_fun`
  + definition `Lspace` with notation `mu.-Lspace p`
  + lemma `Lfun_integrable`, `Lfun1_integrable`, `Lfun2_integrable_sqr`, `Lfun2_mul_Lfun1`
  + lemma `Lfun_scale`, `Lfun_cst`,
  + definitions `finLfun`, `Lfun`, `Lfun_key`
  + canonical `Lfun_keyed`
  + lemmas `sub_Lfun_mfun`, `sub_Lfun_finLfun`
  + definition `Lfun_Sub`
  + lemmas `Lfun_rect`, `Lfun_valP`, `LfuneqP`, `finite_norm_cst0`, `mfunP`, `LfunP`,
    `mfun_scaler_closed`
  + lemmas `LnormZ`, `Lfun_submod_closed`
  + lemmas `finite_norm_fine`, `ler_LnormD`,
    `LnormrN`, `fine_Lnormr_eq0`
  + lemma `fine_Lnormr_eq0`
  + lemma `Lfun_subset`, `Lfun_subset12`
  + lemma `Lfun_oppr_closed`
  + lemma `Lfun_addr_closed`
  + lemmas `poweR_Lnorm`, `oppe_Lnorm`
  + lemmas `hoelder_conjugate_div`, `hoelder_div_conjugate`,
    `hoelder_Mconjugate`, `hoelder_conjugateP`,
    `hoelder_conjugate_eq1`, `hoelder_conjugate_eqNy`, `hoelder_conjugate_eqy`,
    `hoelder_conjugateNy`

- in `probability.v`:
  + definition `exponential_pdf`
  + lemmas `exponential_pdf_ge0`, `lt0_exponential_pdf`,
    `measurable_exponential_pdf`, `exponential_pdfE`,
    `in_continuous_exponential_pdf`, `within_continuous_exponential_pdf`
  + definition `exponential_prob`
  + lemmas `derive1_exponential_pdf`, `exponential_prob_itv0c`,
    `integral_exponential_pdf`, `integrable_exponential_pdf`
  + Definition `poisson_pmf`, `poisson_prob`
  + lemmas `poisson_pmf_ge0`, `measurable_poisson_pmf`,
           `measurable_poisson_prob`
  + instance `poisson_prob`
  + lemma `cdf_lebesgue_stieltjes_id`

### Changed

- in `constructive_ereal.v`:
  + `mule` has special cases optimizing computation for +oo and -oo
  + `mule_def` has been rewritten to optimize computation in several cases.

- in `convex.v`:
  + convex combination operator `a <| t |> b` changed from
    `(1-t)a + tb` to `ta + (1-t)b`
  + definition `convex_realDomainType` generalized and
    renamed accordingly `convex_numDomainType`

- in `sequences.v`:
  + change the implicit arguments of lemma `is_cvg_series_exp_coeff`

- in `tvs.v`:
  + HB class `UniformZmodule` now contains `TopologicalZmodule`
  + HB class `UniformLmodule` now contains `TopologicalLmodule`

- in `measure.v`:
  + definition `pushforward` (to take a function instead of a proof)
  + change the implicit arguments of lemma `measurability`
  + notation `{ae mu, P}` (near use `{near _, _}` notation)
  + definition `ae_eq`
  + `ae_eq` lemmas now for `ringType`-valued functions (instead of `\bar R`)

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_abs_eq0` (remove redundant hypotheses)

- in `lebesgue_integral_differentiation.v`:
  + definition `iavg` (to use `inve`)

- in `measure.v`:
  + fourth argument of `probability_setT` is now explicit

- moved from `measurable_realfun.v` to `lebesgue_stieltjes_measure.v`:
  + definitions `measurableTypeR`, `measurableR`
  + lemmas `measurable_set1`, `measurable_itv`

- in `measure.v`:
  + definition `ess_sup` moved to `ess_sup_inf.v`

### Renamed

- in `convex.v`:
  + lemma `conv_gt0` to `convR_gt0`

- in `tvs.v`:
  + HB class `TopologicalNmodule` moved to `PreTopologicalNmodule`
  + HB class `TopologicalZmodule` moved to `PreTopologicalZmodule`
  + HB class `TopologicalLmodule` moved to `PreTopologicalLmodule`
  + structure `topologicalLmodule` moved to `preTopologicalLmodule`
  + HB class `UniformNmodule` moved to `PreUniformNmodule`
  + HB class `UniformZmodule` moved to `PreUniformZmodule`
  + HB class `UniformLmodule` moved to `PreUniformLmodule`

- in `normed_module.v`:
  + `cvgZl` -> `cvgZr_tmp`
  + `is_cvgZl` -> `is_cvgZr_tmp`
  + `cvgZr` -> `cvgZl_tmp`
  + `is_cvgZr` -> `is_cvgZl_tmp`
  + `is_cvgZrE` -> `is_cvgZlE`
  + `cvgMl` -> `cvgMr_tmp`
  + `cvgMr` -> `cvgMl_tmp`
  + `is_cvgMr` -> `is_cvgMl_tmp`
  + `is_cvgMrE` -> `is_cvgMlE_tmp`
  + `is_cvgMl` -> `is_cvgMr_tmp`
  + `is_cvgMlE` -> `is_cvgMrE_tmp`
  + `limZl` -> `limZr_tmp`
  + `limZr` -> `limZl_tmp`
  + `continuousZr` -> `continuousZl_tmp`
  + `continuousZl` -> `continuousZr_tmp`

- in `realfun.v`:
  + `variationD` -> `variation_cat`

- in `lebesgue_integral_fubini.v`:
  + `fubini1` -> `integral12_prod_meas1`
  + `fubini2` -> `integral21_prod_meas1`

- in `lebesgue_integrable.v`:
  + `integral_fune_lt_pinfty` -> `integrable_lty`
  + `integral_fune_fin_num` -> `integrable_fin_num`

- in `hoelder.v`:
  + `minkowski` -> `minkowski_EFin`

### Generalized

- in `convex.v`:
  + parameter `R` of `convType` from `realDomainType` to `numDomainType`

- in `derive.v`:
  + `derive_cst`, `derive1_cst`
  + lemmas `is_deriveX`, `deriveX`, `exp_derive`, `exp_derive1`

- in `lebesgue_integrable.v`:
  + lemma `integrable_sum`

- in `hoelder.v`:
  + definition `Lnorm` generalized to functions with codomain `\bar R`
    (this impacts the notation `'N_p[f]`)
  + lemmas `Lnorm1`, `eq_Lnorm`, `Lnorm_counting` (from `f : _ -> R` to `f : _ -> \bar R`)

- in `probability.v`:
  + lemma `cantelli`
  + lemmas `expectation_fin_num`, `expectationZl`, `expectationD`, `expectationB`, `expectation_sum`,
    `covarianceE`, `covariance_fin_num`, `covarianceZl`, `covarianceZr`, `covarianceNl`,
    `covarianceNr`, `covarianceNN`, `covarianceDl`, `covarianceDr`, `covarianceBl`, `covarianceBr`,
     `varianceE`, `variance_fin_num`, `varianceZ`, `varianceN`, `varianceD`, `varianceB`,
     `varianceD_cst_l`, `varianceD_cst_r`, `varianceB_cst_l`, `varianceB_cst_r`, `covariance_le`

### Deprecated

- in `set_interval.v`:
  + lemma `mem_1B_itvcc`

### Removed

- in `constructive_ereal.v`:
  + notations `lee_addl`, `lee_addr`, `lee_add2l`, `lee_add2r`, `lee_add`,
    `lee_sub`, `lee_add2lE`, `lee_oppl`, `lee_oppr`, `lte_oppl`, `lte_oppr`,
    `lte_add`, `lte_add2lE`, `lte_addl`, `lte_addr` (deprecated since 1.1.0)

- in `exp.v`:
  + notation `expRMm` (deprecated since 1.1.0)

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`
  + notations `sub_additive`, `sigma_sub_additive`, `content_sub_additive`,
    `ring_sigma_sub_additive`, `Content_SubSigmaAdditive_isMeasure.Build`,
    `measure_sigma_sub_additive`, `measure_sigma_sub_additive_tail`,
    `Measure_isSFinite_subdef.Build`, `sfinite_measure_subdef`,
    `@SigmaFinite_isFinite.Build`, `FiniteMeasure_isSubProbability.Build`
    (deprecated since 1.1.0)

## [1.11.0] - 2025-05-02

### Added

- in `unstable.v`:
  + lemmas `eq_exists2l`, `eq_exists2r`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`

- in `mathcomp_extra.v`:
  + lemmas `inr_inj`, `inl_inj`

- in `boolp.v`:
  + lemmas `orW`, `or3W`, `or4W`

- in `classical_sets.v`:
  + lemmas `in_set1`, `inr_in_set_inr`, `inl_in_set_inr`, `mem_image`, `mem_range`, `image_f`
  + lemmas `inr_in_set_inl`, `inl_in_set_inl`
  + lemmas `set_cst`, `image_nonempty`

- in `functions.v`:
  + lemma `natmulfctE`

- in `constructive_ereal.v`:
  + lemma `EFin_bigmax`
  + lemmas `expe_ge0`, `expe_eq0`, `expe_gt0`

- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`
  + lemmas `ereal_sup_cst`, `ereal_inf_cst`,
    `ereal_sup_pZl`, `ereal_supZl`, `ereal_inf_pZl`, `ereal_infZl`

- in `sequences.v`:
  + lemmas `ereal_inf_seq`, `ereal_sup_seq`

- in `realfun.v`:
  + lemma `cvge_ninftyP`

- in `exp.v`:
  + lemma `poweRE`
  + lemmas `lnNy`, `powR_cvg0`, `derivable_powR`, `powR_derive1`
  + Instance `is_derive1_powR`

- in `measure.v`:
  + lemmas `mnormalize_id`, `measurable_fun_eqP`

- in `lebesgue_integral_approximation.v` (now `measurable_fun_approximation.v`):
  + lemma `measurable_prod`
  + lemma `measurable_fun_lte`
  + lemma `measurable_fun_lee`
  + lemma `measurable_fun_eqe`
  + lemma `measurable_poweR`

- in `ftc.v`:
  + lemma `integrable_locally`

- in `probability.v`:
  + lemmas `eq_bernoulli`, `eq_bernoulliV2`

### Changed

- in `pi_irrational`:
  + definition `rational`

### Renamed

- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`

- in `ereal.v`:
  + `ereal_sup_le` -> `ereal_sup_ge`

- in `pseudometric_normed_Zmodule.v`:
  + `opp_continuous` -> `oppr_continuous`

- in `lebesgue_integral_approximation.v` (now `measurable_fun_approximation.v`):
  + `emeasurable_fun_lt` -> `measurable_lte`
  + `emeasurable_fun_le` -> `measurable_lee`
  + `emeasurable_fun_eq` -> `measurable_lee`
  + `emeasurable_fun_neq` -> `measurable_neqe`

- file `lebesgue_integral_approximation.v` -> `measurable_fun_approximation.v`

### Generalized

- in `functions.v`:
  + `fct_sumE`, `addrfctE`, `sumrfctE` (from `zmodType` to `nmodType`)
  + `scalerfctE` (from `pointedType` to `Type`)

- in `normedtype.v`:
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`

- in `measurable_realfun.v`
  + lemma `measurable_ln`

### Removed

- in `functions.v`:
  + definitions `fct_ringMixin`, `fct_ringMixin` (was only used in an `HB.instance`)

- in `constructive_ereal.v`:
  + notations `esum_ninftyP`, `esum_ninfty`, `esum_pinftyP`, `esum_pinfty` (deprecated since 0.6.0)

- in `pseudometric_structure.v`:
  + notations `cvg_ballPpos`, `app_cvg_locally` (deprecated since 0.6.0)

- in `product_topology.v`:
  + notation `compact_setM` (deprecated since 0.6.0)

- in `separation_axioms.v`:
  + notations `cvg_map_lim`, `cvgi_map_lim` (deprecated since 0.6.6)

- in `sequences.v`:
  + notation `nonincreasing_cvg_ge` (deprecated since 0.6.6)
  + notation `nondecreasing_cvg_le` (deprecated since 0.6.6)
  + notations `nonincreasing_cvg`, `nondecreasing_cvg`, `nonincreasing_is_cvg`,
    `nondecreasing_is_cvg`, `nondecreasing_dvg_lt`, `near_nondecreasing_is_cvg`,
    `near_nonincreasing_is_cvg` (deprecated since 0.6.6)
  + notation `ereal_nondecreasing_opp` (deprecated since 0.6.6)
  + notations `ereal_nondecreasing_cvg`, `ereal_nondecreasing_is_cvg`, `ereal_nonincreasing_cvg`,
    `ereal_nonincreasing_is_cvg` (deprecated since 0.6.6)
  + notations `lim_sup`, `lim_inf`, `lim_infN`, `lim_supE`, `lim_infE`, `lim_inf_le_lim_sup`,
    `cvg_lim_infE`, `cvg_lim_supE`, `le_lim_supD`, `le_lim_infD`, `lim_supD`, `lim_infD`
  + notations `lim_einf_shift`, `lim_esup_le_cvg`, `lim_einfN`, `lim_esupN`, `lim_einf_sup`,
    `cvgNy_lim_einf_sup`, `cvg_lim_einf_sup`, `is_cvg_lim_einfE`, `is_cvg_lim_esupE`

- in `exp.v`:
  + notation `gt0_ler_powR` (deprecated since 0.6.5)

- in `measure.v`:
  + notation `measurable_fun_ext` (deprecated since 0.6.2)
  + notations `measurable_fun_id`, `measurable_fun_cst`, `measurable_fun_comp` (deprecated since 0.6.3)
  + notation `measurable_funT_comp` (deprecated since 0.6.3)

- in `measurable_realfun.v`:
  + notation `measurable_fun_ln` (deprecated since 0.6.3)
  + notations `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd` (deprecated since 0.6.2)
  + notation `measurable_fun_lim_sup` (deprecated since 0.6.6)
  + notation `measurable_fun_max` (deprecated since 0.6.3)
  + notation `measurable_fun_er_map` (deprecated since 0.6.3)
  + notations `emeasurable_funN`, `emeasurable_fun_max`, `emeasurable_fun_min`,
    `emeasurable_fun_funepos`, `emeasurable_fun_funeneg` (deprecated since 0.6.3)
  + notation `measurable_fun_lim_esup` (deprecated since 0.6.6)

- in `lebesgue_integral_nonneg.v`:
  + notations `ge0_integralM_EFin`, `ge0_integralM`, `integralM_indic`, `integralM_indic_nnsfun`
    (deprecated since 0.6.4)

- in `lebesgue_integrable.v`:
  + notation `integralM` (deprecated since 0.6.4)

## [1.10.0] - 2025-04-21

### Added

- in `interval_inference.v`:
  + definitions `IntItv.exprz`, `Instances.natmul_itv`
  + lemmas `Instances.num_spec_exprz`, `Instances.nat_spec_factorial`
  + canonical instance `Instances.exprz_inum`,
    `Instances.factorial_inum`

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- in `mathcomp_extra.v`:
  + lemmas `exprz_ge0` and `exprz_gt0`
  + lemmas `intrN`, `real_floor_itv`, `real_ge_floor`, `real_ceil_itv`
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

- in `set_interval.v`:
  + lemma `subset_itv`

- in `Rstruct.v`:
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)
  + lemmas `RabsE`, `RdistE`, `sum_f_R0E`, `factE`

- in `Rstruct_topology.v`:
  + lemma `RexpE`

- in `constructive_ereal.v`:
  + definition `iter_mule`
  + lemma `prodEFin`
  + lemmas `EFin_fin_numP`, `EFin_bigmax`

- in `real_interval.v`:
  + lemma `itvNycEbigcap`

- in `sequences.v`:
  + lemmas `nneseriesD1`, `geometric_ge0`

- in `derive.v`:
  + lemmas `derive_shift`, `is_derive_shift`
  + lemma `near_eq_growth_rate`
  + lemmas `derive1Mr`, `derive1Ml`
  + lemmas `ger0_derive1_le`, `ger0_derive1_le_cc`, `ger0_derive1_le_co`,
    `ger0_derive1_le_oc`, `ger0_derive1_le_oo`
  + lemmas `gtr0_derive1_lt`, `gtr0_derive1_lt_cc`, `gtr0_derive1_lt_co`,
    `gtr0_derive1_lt_oc`, `gtr0_derive1_lt_oo`
  + lemmas `ler0_derive1_le`, `ler0_derive1_le_cc`, `ler0_derive1_le_co`,
    `ler0_derive1_le_oc`, `ler0_derive1_le_oo`
  + lemmas `ltr0_derive1_lt`, `ltr0_derive1_lt_cc`, `ltr0_derive1_lt_co`,
    `ltr0_derive1_lt_oc`, `ltr0_derive1_lt_oo`

- in `exp.v`:
  + lemma `expR_sum`
  + lemmas `expR_le1`, `num_spec_expR`, `num_spec_powR`
  + definitions `expR_itv_boundl`, `expR_itv_boundr`, `expR_itv`,
    `powR_itv`
  + canonical instance `expR_inum`, `powR_inum`

- in `trigo.v`:
  + lemma `integral0oo_atan`
  + lemmas `num_spec_sin`, `num_spec_cos`
  + canonical instances `sin_inum`, `cos_inum`

- new directory `normedtype_theory` (that replaces `normedtype.v`) with new files:
  + `complete_normed_module.v`
  + `num_normedtype.v`
  + `ereal_normedtype.v`
  + `pseudometric_normed_Zmodule.v`
  + `matrix_normedtype.v`
  + `urysohn.v`
  + `normed_module.v`
  + `vitali_lemma.v`
  + `normedtype.v`

- in `normed_module.v` (new file):
  + lemma `near0Z`

- in `numfun.v`:
  + lemma `num_spec_indic`
  + canonical instance `indic_inum`
  + lemmas `indicC`, `indic_bigcup`
  + lemma `bounded_indic`

- in `measure.v`:
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`
  + lemma `preimage_set_system_id`
  + lemmas `measurable_fun_pair1`, `measurable_fun_pair2`

- in `realfun.v`:
  + lemmas `cvge_pinftyP`, `nonincreasing_cvge`

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

- in `lebesgue_integral_approximation.v` (new file):
  + lemma `measurable_fun_le`

- in `lebesgue_Rintegral.v` (new file):
  + lemma `RintegralD`

- in `lebesgue_integrable.v` (new file):
  + lemma `integrable_indic_itv`

- in `lebesgue_integral_dominated_convergence.v` (new file):
  + lemma `dominated_cvg` (was previously `Local`)

- in `ftc.v`:
  + lemma `continuity_under_integral`

- in `kernel.v`:
  + mixin `isSigmaFiniteTransitionKernel`, structure `SigmaFiniteTransitionKernel`,
    notations `sigma_finite_kernel`, `R .-sigmafker X ~> Y`
  + mixin `isFiniteTransition`, structure `FiniteTransitionKernel`,
    notations `finite_transition_kernel`, `R .-ftker X ~> Y`
  + lemmas `sprob_kernelP`, `sprob_kernel_le1`
  + definition `kfcomp`, lemmas `kfcompk1`, `kfcompkindic`, `measurable_kfcomp`
  + definitions `kproduct`, `kproduct_snd`
  + lemmas `measurable_kproduct`, `semi_sigma_additive_kproduct`
  + definition `mkproduct`
  + theorem `sigma_finite_mkproduct`
  + definition `kcomp_noparam`
  + lemma `kcomp_noparamE`
  + definition `mkcomp_noparam`
  + theorem `sprob_mkcomp_noparam`

- in `probability.v`:
  + definition `cdf`
  + lemmas `cdf_ge0`, `cdf_le1`, `cdf_nondecreasing`, `cvg_cdfy1`, `cvg_cdfNy0`, `cdf_right_continuous`
  + definitions `normal_fun`, `normal_peak`
  + lemmas `measurable_normal_fun`, `normal_fun_ge0`, `normal_fun_center`
  + lemmas `normal_peak_ge0`, `normal_peak_gt0`
  + lemma `normal_pdfE`
  + lemma `normal_pdf_ge0`, `normal_pdf_ub`
  + lemma `integrable_normal_pdf`

### Changed

- in `interval_inference.v`:
  + definition `IntItv.exprn_le1_bound`
  + lemmas `Instances.nat_spec_succ`, `Instances.num_spec_natmul`,
    `Instances.num_spec_intmul`, `Instances.num_itv_bound_exprn_le1`
  + canonical instance `Instances.succn_inum`

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package

- in `classical_sets.v`:
  + change implicit arguments of `subsetT`

- `topology.v` now exports `separation_axioms`

- file `separation_axioms.v` moved from `theories` to `theories/topology_theory`

- moved from `normedtype.v` (old file) to `num_topology.v`
  + lemmas `nbhsN`, `cvg_compNP`, `nbhsNimage`, `nearN`, `openN`,
    `closedN`, `dnbhsN`, `closure_sup`, `right_bounded_interior`, `left_bounded_interior`,
    `withinN`

- the contents of `normedtype.v` (old file) can be found in the files in directory
  `normed_theory` unless stated otherwise

- in `filter.v`:
  + change implicit arguments of `cvg_comp`

- moved from `gauss_integral` to `trigo.v`:
  + `oneDsqr`, `oneDsqr_ge1`, `oneDsqr_inum`, `oneDsqrV_le1`,
    `continuous_oneDsqr`, `continuous_oneDsqr`

- moved, generalized, and renamed from `gauss_integral` to `trigo.v`:
  + `integral01_oneDsqr` -> `integral0_oneDsqr`

- in `lebesgue_Rintegral.v` (new file):
  + `le_normr_integral` renamed to `le_normr_Rintegral`

- moved to `lebesgue_measure.v` (from old `lebesgue_integral.v`)
  + `compact_finite_measure`

- moved from `ftc.v` to `lebesgue_integral_under.v` (new file):
  + notation `'d1`, definition `partial1of2`, lemmas `partial1of2E`,
    `cvg_differentiation_under_integral`, `differentiation_under_integral`,
    `derivable_under_integral`

- in `probability.v`:
  + definition `normal_pdf` changed to use `normal_fun` and `normal_peak`

### Renamed

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

- in `set_interval.v`:
  + `set_itv_infty_infty` -> `set_itvNyy`
  + `set_itv_o_infty` -> `set_itvoy`
  + `set_itv_c_infty` -> `set_itvcy`
  + `set_itv_infty_o` -> `set_itvNyo`
  + `set_itv_infty_c` -> `set_itvNyc`
  + `set_itv_pinfty_bnd` -> `set_itv_ybnd`
  + `set_itv_bnd_ninfty` -> `set_itv_bndNy`

- in `real_interval.v`:
  + `itv_c_inftyEbigcap` -> `itvcyEbigcap`
  + `itv_bnd_inftyEbigcup` -> `itvbndyEbigcup`
  + `itv_o_inftyEbigcup` -> `itvoyEbigcup`

- in `normed_module.v` (new file):
  + `cvgeMl` -> `cvgeZl`
  + `is_cvgeMl` -> `is_cvgeZl`
  + `cvgeMr` -> `cvgeZr`
  + `is_cvgeMr` -> `is_cvgeZr`

- in `measure.v`:
  + `measurable_fun_prod` -> `measurable_fun_pair`
  + `prod_measurable_funP` -> `measurable_fun_pairP`
  + `measurable_pair1` -> `pair1_measurable`
  + `measurable_pair2` -> `pair2_measurable`

- in `lebesgue_integral_fubini.v` (new file):
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`

- in `simple_functions.v` (new file):
  + `measurable_funP` -> `measurable_funPT` (field of `isMeasurableFun` mixin)

- in `kernel.v`:
  + `Kernel_isSFinite_subdef` -> `isSFiniteKernel_subdef`
  + `SFiniteKernel_isFinite` -> `isMeasureFamUub`
  + `FiniteKernel_isSubProbability` -> `isSubProbabilityKernel`
  + `SubProbability_isProbability` -> `isProbabilityKernel`

### Generalized

- in `constructive_ereal.v`:
  + lemma `EFin_natmul`

- in `real_interval.v`:
  + lemmas `bigcup_itvT`, `itv_bndy_bigcup_BRight`, `itv_bndy_bigcup_BLeft_shift`

- in `sequences.v`:
  + lemma `nneseries_recl` genralized with a filtering predicate `P`

- in `pseudometric_normed_Zmodule.v` (new file):
  + generalized from `normedModType` to `pseudoMetricNormedZmodType`:
    * lemmas `cvgr_norm_lty`, `cvgr_norm_ley`, `cvgr_norm_gtNy`,
      `cvgr_norm_geNy`, `cvg_bounded`

- in `num_normedtype.v` (new file):
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`

- in `ereal_normedtype.v` (new file):
  + `lower_semicontinuous`, `lower_semicontinuousP` generalized from `realType` to `numFieldType`

- in `lebesgue_integral.v`
  + lemmas `measurable_funP`, `ge0_integral_pushforward`,
    `integrable_pushforward`, `integral_pushforward`

### Deprecated

- in `normedtype.v` (old file):
  + `pseudoMetricNormedZModType_hausdorff` (use `norm_hausdorff` instead)

- in `derive.v`:
  + `ler0_derive1_nincr` (use `ler0_derive1_le_cc` instead)
  + `gtr0_derive1_incr` (use `gtr0_le_derive1` instead)

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

- in `classical_sets.v`:
  + notations `setvI`, `setIv`, `bigcup_set`, `bigcup_set_cond`, `bigcap_set`,
    `bigcap_set_cond`

- in `filter.v`:
  + definition `at_point` (redundant with `principal_filter`)

- in `reals.v`:
  + lemmas `floor_le`, `le_floor` (deprecated since 1.3.0)

- in `measure.v`:
  + notations `measurable_fun_fst`, `measurable_fun_snd`, `measurable_fun_swap`
    (deprecated since 0.6.3)

- file `lebesgue_integral.v` (split in several files in the directory
  `lebesgue_integral_theory`)

- file `normedtype.v` (split in several files in the directory
  `normed_theory`)

## [1.9.0] - 2025-02-20

### Added

- in `mathcomp_extra.v`:
  + lemmas `prodr_ile1`, `nat_int`
  + lemmas `size_filter_gt0`, `ltr_sum`, `ltr_sum_nat`
  + lemmas `comparable_BSide_min`, `BSide_min`, `BSide_max`,
    `real_BSide_min`, `real_BSide_max`, `natr_min`, `natr_max`,
    `comparable_min_le_min`, `comparable_max`, `min_le_min`,
    `max_le_max` and `real_sqrtC`

- in `classical_sets.v`:
  + lemmas `xsectionE`, `ysectionE`
  + lemma `itv_sub_in2`

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
  + definitions `ItvReal` and `Itv01`
  + lemmas `cmp0`, `neq0`, `eq0F`, `num_min`, `num_max`
  + notation `%:num`
  + notations `{posnum R}`, `{nonneg R}`, `%:pos`, `%:nng`,
    `%:posnum`, `%:nngnum`, `[gt0 of _]`, `[lt0 of _]`, `[ge0 of _]`,
    `[le0 of _]`, `[cmp0 of _]`, `[neq0 of _]`
  + definitions `PosNum` and `NngNum`

- in `constructive_ereal.v`:
  + lemma `abse_EFin`
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

- in `set_interval.v`:
  + lemma `set_itv_splitU`

- in `ereal.v`:
  + lemmas `ext_num_spec_ereal_sup`, `ext_num_spec_ereal_inf`
  + canonicals `ereal_sup_inum`, `ereal_inf_inum`

- in `topology_theory/topological_structure.v`
  + lemmas `interior_id`, `interiorT`, `interior0`, `closureT`

- in `topology_theory/num_topology.v`:
  + lemmas `lt_nbhsl`, `Nlt_nbhsl`
  + lemma `lt_nbhsr`

- in `normedtype.v`:
  + lemma `scaler1`
  + lemma `nbhs_right_leftP`
  + lemmas `bounded_cst`, `subr_cvg0`
  + lemma `cvgr_expr2`, `cvgr_idn`
  + lemmas `ninfty`, `cvgy_compNP`
  + global hint to automatically apply `interval_open`
  + lemmas `cvg_compNP`, `decreasing_itvNyo_bigcup`, `decreasing_itvoo_bigcup`,
    `increasing_itvNyo_bigcup`, `increasing_itvoc_bigcup`
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`

- in `sequences.v`:
  + lemma `seqDUE`
  + lemma `nondecreasing_telescope_sumey`

- in `derive.v`:
  + lemmas `horner0_ext`, `hornerD_ext`, `horner_scale_ext`, `hornerC_ext`,
    `derivable_horner`, `derivE`, `continuous_horner`
  + instance `is_derive_poly`
  + lemmas `decr_derive1_le0`, `decr_derive1_le0_itv`,
           `decr_derive1_le0_itvy`, `decr_derive1_le0_itvNy`,
           `incr_derive1_ge0`, `incr_derive1_ge0_itv`,
           `incr_derive1_ge0_itvy`, `incr_derive1_ge0_itvNy`,
  + lemmas `ler0_derive1_nincry`, `ger0_derive1_ndecry`,
           `ler0_derive1_nincrNy`, `ger0_derive1_ndecrNy`
  + lemmas `ltr0_derive1_decr`, `gtr0_derive1_incr`
  + lemmas `near_eq_derivable`, `near_eq_derive`, `near_eq_is_derive`
  + lemmas `derive1N`, `derivable_opp`, `derive1_id`

- in `real_interval.v`:
  + lemma `itv_bnd_infty_bigcup0S`
  + lemma `itv_bndy_bigcup_BLeft_shift`

- in `numfun.v`
  + lemmas `funeposE`, `funenegE`, `funepos_comp`, `funeneg_comp`

- in `trigo.v`:
  + lemma `derivable_atan`

- in `realfun.v`:
  + definition `discontinuity`
  + lemmas `nondecreasing_fun_sum_le`, `discontinuty_countable`
  + definitions `derivable_Nyo_continuous_bnd`, `derivable_oy_continuous_bnd `
  + lemma `cvg_addrr_Ny`
  + lemmas `lhopital_at_left`, `lhopital_at_left`, `lhopital`,

- new file `measurable_realfun.v`
  + with as contents the first half of the file `lebesgue_measure.v`
  + lemmas `measurable_fun_itv_bndo_bndc`, `measurable_fun_itv_obnd_cbnd`

- in `lebesgue_integral.v`:
  + lemmas `integral_fin_num_abs`, `Rintegral_cst`, `le_Rintegral`
  + lemma `integral_bigsetU_EFin`
  + lemmas `interior_itv_bnd`, `interior_itv_bndy`, `interior_itv_Nybnd`,
    definition `interior_itv`
  + lemma `interior_set1`
  + lemmas `interior_itv_bnd`, `interior_itv_bndy`, `interior_itv_Nybnd`, `interior_itv_Nyy`
  + definition `interior_itv`
  + lemma `RintegralB`
  + lemma `ge0_cvgn_integral`

- in `ftc.v`:
  + lemmas `differentiation_under_integral`, `derivable_under_integral`
  + definition `partial1of2`, lemma `partial1of2E`
  + lemma `ge0_continuous_FTC2y`
  + lemma `Rintegral_ge0_continuous_FTC2y`
  + lemma `le0_continuous_FTC2y`
  + lemmas `decreasing_ge0_integration_by_substitutiony`,
    `ge0_integration_by_substitutionNy`,
    `increasing_ge0_integration_by_substitutiony`,
    `ge0_integration_by_substitutionNy`,
    `increasing_ge0_integration_by_substitutionT`,
    `ge0_symfun_integralT`

- in `probability.v`:
  + definition `normal_pdf`
  + lemmas `normal_pdf_ge0`, `normal_pdf_gt0`, `measurable_normal_pdf`,
    `continuous_normal_pdf`, `normal_pdf_ub`
  + definition `normal_prob`, equipped with the structure of probability measure
  + lemmas `integral_normal_pdf`, `normal_prob_dominates`

- new file `pi_irrational.v`:
  + lemmas `measurable_poly`
  + definition `rational`
  + module `pi_irrational`
  + lemma `pi_irrationnal`

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
  + lemmas `integralT_gauss`, `integrableT_gauss`

### Changed

- in `Rstruct.v`
  + instantiate `GRinv.inv` by `Rinv` instead of `Rinvx`

- file `interval_inference.v`
  + definitions `Itv.def`, `Itv.spec`, `Itv.typ`, `empty_itv`

- moved from `topology_structure.v` to `discrete_topology.v`:
  `discrete_open`, `discrete_set1`, `discrete_closed`, and `discrete_cvg`.

- in `cantor.v`, `cantor_space` now defined in terms of `bool`

- moved from `pseudometric_structure.v` to `discrete_topology.v`:
    `discrete_ent`, `discrete_ball`, and `discrete_topology`.

- in `separation_axioms.v`, updated `discrete_hausdorff`, and
    `discrete_zero_dimension` to take a `discreteTopologicalType`

- moved from `normedtype.v` to `num_topology.v` and renamed:
  + `nbhs_lt` -> `lt_nbhsl_lt`
  + `nbhs_le` -> `lt_nbhsl_le`

- in `normedtype.v`:
  + lemma `cvgyNP` renamed to `cvgNy_compN` and generalized

- in `numfun.v`
  + lock `funepos`, `funeneg`

- in `derive.v`:
  + put the notation ``` ^`() ``` and ``` ^`( _ ) ``` in scope `classical_set_scope`

- in `measure.v`:
  + `content_snum` -> `content_inum`
  + `measure_snum` -> `measure_inum`

- file `lebesgue_measure.v`
  + first half moved to a new file `measurable_realfun.v`

- moved from `lebesgue_integral.v` to `measure.v` and generalized
  + lemmas `measurable_xsection`, `measurable_ysection`

- in `lebesgue_integral.v`
  + change implicits of `measurable_funP`

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

- in `set_interval.v`:
  + `opp_itv_bnd_infty` -> `opp_itv_bndy`
  + `opp_itv_infty_bnd` -> `opp_itvNy_bnd`

- in `real_interval.v`:
  + `itv_bnd_infty_bigcup` -> `itv_bndy_bigcup_BRight`
  + `itv_bnd_infty_bigcup0S` -> `itv0y_bigcup0S`
  + `itv_infty_bnd_bigcup` -> `itvNy_bnd_bigcup_BLeft`

- in `normedtype.v`:
  + `cvge_sub0` -> `sube_cvg0`

- in `measure.v`
  + `preimage_class` -> `preimage_set_system`
  + `image_class` -> `image_set_system`
  + `preimage_classes` -> `g_sigma_preimageU`
  + `preimage_class_measurable_fun` -> `preimage_set_system_measurable_fun`
  + `sigma_algebra_preimage_class` -> `sigma_algebra_preimage`
  + `sigma_algebra_image_class` -> `sigma_algebra_image`
  + `sigma_algebra_preimage_classE` -> `g_sigma_preimageE`
  + `preimage_classes_comp` -> `g_sigma_preimageU_comp`
  + `setDI_closed` -> `setD_closed`
  + `setDI_semi_setD_closed` -> `setD_semi_setD_closed`
  + `sedDI_closedP` -> `setD_closedP`
  + `setringDI` -> `setringD`

- in `lebesgue_integral.v`:
  + `Rintegral_setU_EFin` -> `Rintegral_setU`

### Generalized

- in `Rstruct.v`:
  + lemma `RsqrtE`

- in `constructive_ereal.v`:
  + generalized from `realDomainType` to `numDomainType`
    * lemmas `EFin_min` and `EFin_max`
    * lemmas `maxye`, `maxeNy`, `mineNy`, `minye`

- in `normedtype.v`:
  + lemmas `not_near_at_rightP`, `not_near_at_leftP`
  + `cvg_at_right_filter`, `cvg_at_left_filter`
  + lemma `open_subball`
  + lemma `interval_unbounded_setT`

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

- file `signed.v` (use `interval_inference.v` instead)

- in `interval_inference.v`:
  + notation `%:inum` (use `%:num` instead)

- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_itv_co`, `measurable_fun_itv_oc`

### Removed

- in `topology_structure.v`, removed `discrete_sing`, `discrete_nbhs`, and `discrete_space`

- in `nat_topology.v`, removed `discrete_nat`

- in `pseudometric_structure.v`, removed `discrete_ball_center`, `discrete_topology_type`,
  and `discrete_space_discrete`.

- in `signed.v/interval_inference.v`
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

- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)
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

- in `normedtype.v`
  + notations `cvg_distP`, `cvg_distW`, `continuous_cvg_dist`, `cvg_dist2P`,
    `cvg_gt_ge`, `cvg_lt_le_`, `linear_bounded0`
    (deprecated since 0.6.0)
  + lemmas `__deprecated__cvg_distW`, `__deprecated__continuous_cvg_dist`,
    `__deprecated__cvg_gt_ge`, `__deprecated__cvg_lt_le`,
    `__deprecated__linear_bounded0 `
    (deprecated since 0.6.0)
  + notations `cvg_distP`, `cvg_distW`, `continuous_cvg_dist`, `cvg_dist2P`,
    `cvg_gt_ge`, `cvg_lt_le_`, `linear_bounded0`
    (were deprecated since 0.6.0)
  + lemmas `__deprecated__cvg_distW`, `__deprecated__continuous_cvg_dist`,
    `__deprecated__cvg_gt_ge`, `__deprecated__cvg_lt_le`,
    `__deprecated__linear_bounded0`
    (were deprecated since 0.6.0)

- in `derive.v`:
  + notations `le0r_cvg_map`, `ler0_cvg_map`, `ler_cvg_map`
    (deprecated since 0.6.0)
  + lemmas `__deprecated__le0r_cvg_map`, `__deprecated__ler0_cvg_map`,
    `__deprecated__ler_cvg_map`
    (deprecated since 0.6.0)

- in `measure.v`:
  + notation `caratheodory_lim_lee` (was deprecated since 0.6.0)

- in `lebesgue_measure.v`:
  + notations `itv_cpinfty_pinfty`, `itv_opinfty_pinfty`, `itv_cninfty_pinfty`,
    `itv_oninfty_pinfty` (were deprecated since 0.6.0)
  + lemmas `__deprecated__itv_cpinfty_pinfty`, `__deprecated__itv_opinfty_pinfty`,
    `__deprecated__itv_cninfty_pinfty`, `__deprecated__itv_oninfty_pinfty`
    (were deprecated since 0.6.0)

## [1.8.0] - 2024-12-19

### Added

- in `mathcomp_extra.v`:
  + lemma `partition_disjoint_bigfcup`

- in `constructive_ereal.v`:
  + notations `\prod` in scope ereal_scope
  + lemmas `prode_ge0`, `prode_fin_num`

- in `num_topology.v`:
  + lemma `in_continuous_mksetP`

- in `normedtype.v`:
  + lemmas `continuous_within_itvcyP`, `continuous_within_itvNycP`

- in `realfun.v`:
  + lemma `cvg_nbhsP`

- in `measure.v`:
  + lemma `countable_bigcupT_measurable`
  + definition `discrete_measurable`
  + lemmas `discrete_measurable0`, `discrete_measurableC`, `discrete_measurableU`

- in `lebesgue_measure.v`:
  + lemma `measurable_indicP`
  + lemma `measurable_powRr`

- in `lebesgue_integral.v`:
  + definition `dyadic_approx` (was `Let A`)
  + definition `integer_approx` (was `Let B`)
  + lemma `measurable_sum`
  + lemma `integrable_indic`
  + lemmas `integrable_pushforward`, `integral_pushforward`
  + lemma `integral_measure_add`

- in `probability.v`:
  + lemma `expectation_def`
  + notation `'M_`
  + lemma `integral_distribution` (existing lemma `integral_distribution` has been renamed)

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`

### Renamed

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

- file `homotopy_theory/path.v` -> `homotopy_theory/continuous_path.v`

- in `lebesgue_measure.v`:
  + `measurable_fun_indic` -> `measurable_indic`
  + `emeasurable_fun_sum` -> `emeasurable_sum`
  + `emeasurable_fun_fsum` -> `emeasurable_fsum`
  + `ge0_emeasurable_fun_sum` -> `ge0_emeasurable_sum`

- in `probability.v`:
  + `expectationM` -> `expectationZl`
  + `integral_distribution` -> `ge0_integral_distribution`

### Generalized

- in `sequences.v`:
  + lemmas `cvg_restrict`, `cvg_centern`, `cvg_shiftn cvg_shiftS`

- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`

- in `probability.v`:
  + definition `random_variable`
  + lemmas `notin_range_measure`, `probability_range`
  + definition `distribution`
  + lemma `probability_distribution`, `integral_distribution`
  + mixin `MeasurableFun_isDiscrete`
  + structure `discreteMeasurableFun`
  + definition `discrete_random_variable`
  + lemma `dRV_dom_enum`
  + definitions `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV`, `sum_enum_prob`

### Deprecated

- in `lebesgue_integral.v`:
  + lemma `approximation`

### Removed

- in `constructive_ereal.v`
  + notation `lee_opp` (deprecated since 0.6.5)
  + notation `lte_opp` (deprecated since 0.6.5)

- in `measure.v`:
  + `dynkin_setI_bigsetI` (use `big_ind` instead)

- in `lebesgue_measurable.v`:
  + notation `measurable_fun_power_pos` (deprecated since 0.6.3)
  + notation `measurable_power_pos` (deprecated since 0.6.4)

- in `lebesgue_integral.v`:
  + lemma `measurable_indic` (was uselessly specializing `measurable_fun_indic` (now `measurable_indic`) from `lebesgue_measure.v`)
  + notation `measurable_fun_indic` (deprecation since 0.6.3)

## [1.7.0] - 2024-11-22

### Added

- package `coq-mathcomp-reals` depending on `coq-mathcomp-classical`
  with files
  + `constructive_ereal.v`
  + `reals.v`
  + `real_interval.v`
  + `signed.v`
  + `itv.v`
  + `prodnormedzmodule.v`
  + `nsatz_realtype.v`
  + `all_reals.v`

- package `coq-mathcomp-experimental-reals` depending on `coq-mathcomp-reals`
  with files
  + `xfinmap.v`
  + `discrete.v`
  + `realseq.v`
  + `realsum.v`
  + `distr.v`

- package `coq-mathcomp-reals-stdlib` depending on `coq-mathcomp-reals`
  with file
  + `Rstruct.v`

- package `coq-mathcomp-analysis-stdlib` depending on
  `coq-mathcomp-analysis` and `coq-mathcomp-reals-stdlib` with files
  + new file `Rstruct_topology.v`
  + `showcase/uniform_bigO.v`

- in file `mathcomp_extra.v`:
  + definition `sigT_fun`
  + definition `idempotent_fun`

- in `boolp.v`:
  + lemmas `existT_inj1`, `surjective_existT`
  + lemma `existT_inj2`
  + new lemmas `uncurryK`, and `curryK`

- new file `topology_theory/one_point_compactification.v`:
  + definitions `one_point_compactification`, and `one_point_nbhs`.
  + lemmas `one_point_compactification_compact`,
    `one_point_compactification_some_nbhs`,
    `one_point_compactification_some_continuous`,
    `one_point_compactification_open_some`,
    `one_point_compactification_weak_topology`, and
    `one_point_compactification_hausdorff`.

- new file `topology_theory/sigT_topology.v`:
  + definition `sigT_nbhs`.
  + lemmas `sigT_nbhsE`, `existT_continuous`, `existT_open_map`,
    `existT_nbhs`, `sigT_openP`, `sigT_continuous`, `sigT_setUE`, and
    `sigT_compact`.

- in file `topology_theory/product_topology.v`:
  + lemmas `swap_continuous`, `prodA_continuous`, and
    `prodAr_continuous`.

- in file `topology_theory/order_topology.v`:
  + lemmas `min_continuous`, `min_fun_continuous`, `max_continuous`, and
    `max_fun_continuous`.

- in file `topology_theory/weak_topology.v`:
  + lemma `continuous_comp_weak`

- in `topology_theory/topology_structure.v`:
  + definitions `regopen`, `regclosed`
  + lemmas `closure_setC`, `interiorC`, `closureU`, `interiorU`,
           `closureEbigcap`, `interiorEbigcup`,
	   `closure_open_regclosed`, `interior_closed_regopen`,
	   `closure_interior_idem`, `interior_closure_idem`
  + mixin `isContinuous`, type `continuousType`, structure `Continuous`
  + lemma `continuousEP`
  + definition `mkcts`

- in file `topology_theory/subspace_topology.v`:
  + lemmas `continuous_subspace_setT`, `nbhs_prodX_subspace_inE`, and
    `continuous_subspace_prodP`.
  + type `continuousFunType`, HB structure `ContinuousFun`

- in file `topology_theory/subtype_topology.v`:
  + lemmas `subspace_subtypeP`, `subspace_sigL_continuousP`,
    `subspace_valL_continuousP'`, `subspace_valL_continuousP`, `sigT_of_setXK`,
    `setX_of_sigTK`, `setX_of_sigT_continuous`, and `sigT_of_setX_continuous`.

- in file `separation_axioms.v`:
  + lemmas `compact_normal_local`, and `compact_normal`.
  + lemma `sigT_hausdorff`.

- in file `function_spaces.v`:
  + definition `eval`
  + lemmas `continuous_curry_fun`, `continuous_curry_cvg`,
    `eval_continuous`, and `compose_continuous`

- new file `tvs.v`:
  + HB structures `NbhsNmodule`, `NbhsZmodule`, `NbhsLmodule`, `TopologicalNmodule`,
    `TopologicalZmodule`
  + notation `topologicalLmoduleType`, HB structure `TopologicalLmodule`
  + HB structures `UniformZmodule`, `UniformLmodule`
  + definition `convex`
  + mixin `Uniform_isTvs`
  + type `tvsType`, HB structure `Tvs`
  + HB factory `TopologicalLmod_isTvs`
  + lemma `nbhs0N`
  + lemma `nbhsN`
  + lemma `nbhsT`
  + lemma `nbhsB`
  + lemma `nbhs0Z`
  + lemma `nbhZ`

- in file `normedtype.v`:
  + definition `type` (in module `completely_regular_uniformity`)
  + lemmas `normal_completely_regular`,
    `one_point_compactification_completely_reg`,
    `nbhs_one_point_compactification_weakE`,
    `locally_compact_completely_regular`, and
    `completely_regular_regular`.
  + lemmas `near_in_itvoy`, `near_in_itvNyo`

- in `measure.v`:
  + lemma `countable_measurable`

- in `realfun.v`:
  + lemma `cvgr_dnbhsP`
  + definitions `prodA`, and `prodAr`
  + lemmas `prodAK`, `prodArK`, and `swapK`

- new file `homotopy_theory/path.v`:
  + definitions `reparameterize`, `mk_path`, and `chain_path`.
  + lemmas `path_eqP`, and `chain_path_cts_point`.

- new file `homotopy_theory/wedge_sigT.v`:
  + definitions `wedge_rel`, `wedge`, `wedge_lift`, `pwedge`.
  + lemmas `wedge_lift_continuous`, `wedge_lift_nbhs`,
    `wedge_liftE`, `wedge_openP`,
    `wedge_pointE`, `wedge_point_nbhs`, `wedge_nbhs_specP`, `wedgeTE`,
    `wedge_compact`, `wedge_connected`.
  + definitions `wedge_fun`, and `wedge_prod`.
  + lemmas `wedge_fun_continuous`, `wedge_lift_funE`,
    `wedge_fun_comp`, `wedge_prod_pointE`, `wedge_prod_inj`,
    `wedge_prod_continuous`, `wedge_prod_open`, `wedge_hausdorff`, and
    `wedge_fun_joint_continuous`.
  + definition `bpwedge_shared_pt`.
  + notations `bpwedge`, and `bpwedge_lift`.

- new file `homotopy_theory/homotopy.v`

### Changed

- moved from `Rstruct.v` to `Rstruct_topology.v`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`,
    `continuity_ptE`, `continuity_pt_cvg'`, `continuity_pt_dnbhs`
    and `nbhs_pt_comp`

- moved from `real_interval.v` to `normedtype.v`
  + lemmas `set_itvK`, `RhullT`, `RhullK`, `set_itv_setT`,
    `Rhull_smallest`, `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`,
    `disj_itv_Rhull`

- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in file `normedtype.v`:
  + changed `completely_regular_space` to depend on uniform separators
    which removes the dependency on `R`.  The old formulation can be
    recovered easily with `uniform_separatorP`.
  + HB structure `normedModule` now depends on a Tvs
    instead of a Lmodule
  + Factory `PseudoMetricNormedZmod_Lmodule_isNormedModule` becomes
    `PseudoMetricNormedZmod_Tvs_isNormedModule`
  + Section `prod_NormedModule` now depends on a `numFieldType`

- in `lebesgue_integral.v`:
  + structure `SimpleFun` now inside a module `HBSimple`
  + structure `NonNegSimpleFun` now inside a module `HBNNSimple`
  + lemma `cst_nnfun_subproof` has now a different statement
  + lemma `indic_nnfun_subproof` has now a different statement

### Renamed

- in `normedtype.v`:
  + `near_in_itv` -> `near_in_itvoo`
  + Section `regular_topology` to `standard_topology`

### Generalized

- in `lebesgue_integral.v`:
  + generalized from `sigmaRingType`/`realType` to `sigmaRingType`/`sigmaRingType`
    * mixin `isMeasurableFun`
    * structure `MeasurableFun`
	* definition `mfun`
    * lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`

### Deprecated

- in `topology_theory/topology_structure.v`:
  + lemma `closureC`

### Removed

- in `cardinality.v`:
  + lemma `cst_fimfun_subproof`

- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`
  + lemma `cst_mfun_subproof` (use lemma `measurable_cst` instead)
  + lemma `cst_nnfun_subproof` (turned into a `Let`)
  + lemma `indic_mfun_subproof` (use lemma `measurable_fun_indic` instead)

## [1.6.0] - 2024-10-25

### Added

- new directory `theories/topology` with new files:
  + `topology.v`
  + `bool_topology.v`
  + `compact.v`
  + `connected.v`
  + `matrix_topology.v`
  + `nat_topology.v`
  + `order_topology.v`
  + `product_topology.v`
  + `pseudometric_structure.v`
  + `subspace_topology.v`
  + `supremum_topology.v`
  + `topology_structure.v`
  + `uniform_structure.v`
  + `weak_topology.v`
  + `num_topology.v`
  + `quotient_topology.v`

- in `exp.v`:
  + lemmas `cvgr_expR`, `cvgn_expR`

- in `trigo.v`:
  + lemmas `derive1_atan`, `lt_atan`, `le_atan`, `cvgy_atan`

- in `lebesgue_measure.v`:
  + lemmas `RintegralZl`, `RintegralZr`, `Rintegral_ge0`

### Changed

- The file `topology.v` has been split into several files in the directory
  `topology_theory`. Unless stated otherwise, definitions, lemmas, etc.
  have been moved without changes. The same import will work as before,
  `Require Import topology.v`.

- in `matrix_topology.v` (new file):
  + lemmas `mx_ball_center`, `mx_ball_sym`, `mx_ball_triangle`, `mx_entourage`
    are now `Local`

- in `weak_topology.v` (new file):
  + lemmas `wopT`, `wopI`, `wop_bigU` are now `Local`

- in `supremum_topology.v` (new file):
  + lemmas `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
    `sup_ent_nbhs` are now `Local`

- The function `map_pair` was moved from `topology.v` to `mathcomp_extra.v`.

- in `forms.v`:
  + notation `'e_`

- in `lebesgue_integral.v`:
  + notation `\x`

### Renamed

- in `lebesgue_measure.v`:
  + `EFin_measurable_fun` -> `measurable_EFinP`

### Generalized

- in `num_topology.v` (new file):
  + lemma `nbhs0_lt` generalized from `realType` to `realFieldType`

### Deprecated

- in `pseudometric_structure.v` (new file):
  + definition `cvg_toi_locally` (use `cvgi_ballP` instead)

### Removed

- file `topology.v` (contents now in directory `topology`)

## [1.5.0] - 2024-10-09

### Added

- in `mathcomp_extra.v`:
  + lemma `bij_forall`

- in `classical_sets.v`:
  + lemma `not_setD1`

- in file `classical_orders.v` (new file),
  + definitions `big_lexi_order`, `same_prefix`, `first_diff`,
    `big_lexi_le`, and `start_with`.
  + lemmas `same_prefix0`, `same_prefix_sym`, `same_prefix_leq`,
    `same_prefix_refl`, `same_prefix_trans`, `first_diff_sym`,
    `first_diff_unique`, `first_diff_SomeP`, `first_diff_NoneP`,
    `first_diff_lt`, `first_diff_eq`, `first_diff_dfwith`,
    `big_lexi_le_reflexive`, `big_lexi_le_anti`, `big_lexi_le_trans`,
    `big_lexi_le_total`, `start_with_prefix`, `leEbig_lexi_order`,
    `big_lexi_order_prefix_lt`, `big_lexi_order_prefix_gt`,
    `big_lexi_order_between`, and `big_lexi_order_interval_prefix`.

- in `filter.v` (new file):
  + lemma `in_nearW`

- in `topology.v`:
  + lemma `open_in_nearW`

- new file `separation_axioms.v`

- in `normedtype.v`:
  + lemma `cvgyNP`
  + lemma `limf_esup_ge0`
  + lemma `nbhs_left_ltBl`
  + lemma `within_continuous_continuous`

- in `sequences.v`:
  + lemma `nneseries_split_cond`
  + lemma `subset_lee_nneseries`

- in `exp.v`:
  + lemma `expR_gt1Dx`

- in `derive.v`:
  + lemma `exprn_derivable`

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

- in `measure.v`:
  + lemma `measurable_fun_set1`
  + lemma `measurable_fun_set0`

- in `lebesgue_measure.v`:
  + lemma `vitali_coverS`
  + lemma `vitali_theorem_corollary`
  + lemmas `measurable_fun_itv_co`, `measurable_fun_itv_oc`, `measurable_fun_itv_cc`

- in `lebesgue_integral.v`:
  + lemma `integral_itv_bndoo`

- in `ftc.v`:
  + lemmas `increasing_image_oo`, `decreasing_image_oo`,
    `increasing_cvg_at_right_comp`, `increasing_cvg_at_left_comp`,
    `decreasing_cvg_at_right_comp`, `decreasing_cvg_at_left_comp`,
  + lemma `eq_integral_itv_bounded`.
  + lemmas `integration_by_substitution_decreasing`,
    `integration_by_substitution_oppr`,
    `integration_by_substitution_increasing`

### Changed

- `theories/topology.v` split into `classical/filter.v` and `theories/topology.v`

- moved from `topology.v` to `filter.v`
  + definition `set_system`, coercion `set_system_to_set`
  + mixin `isFiltered`, structures `Filtered`, `PointedFiltered`
    (with resp. types `filteredType` and `pfilteredType`)
  + mixin `selfFiltered`
  + factory `hasNbhs`
  + structures `Nbhs`, `PointedNbhs`
    (with resp. types `nbhsType`, `pnbhsType`)
  + definitions `filter_from`, `filter_prod`
  + definitions `prop_near1`, `prop_near2`
  + notations `{near _, _}`, `\forall _ \near _, _`, `near _, _`,
    `{near _ & _, _}`, `\forall _ \near _ & _, _`, `\forall _ & _ \near _, _`,
    `\near _ & _, _`
  + lemmas `nearE`, `eq_near`, `nbhs_filterE`
  + module `NbhsFilter` (with definition `nbhs_simpl`)
  + definition `cvg_to`, notation ```_ `=>` _```
  + lemmas `cvg_refl`, `cvg_trans`, notation `_ --> _`
  + definitions `type_of_filter`, `lim_in`, `lim`
  + notations `[lim _ in _]`, `[cvg _ in _]`, `cvg`
  + definition `eventually`, notation `\oo`
  + lemmas `cvg_prod`, `cvg_in_ex`, `cvg_ex`, `cvg_inP`, `cvgP`, `cvg_in_toP`,
    `cvg_toP`, `dvg_inP`, `dvgP`, `cvg_inNpoint`, `cvgNpoint`
  + lemmas `nbhs_nearE`, `near_nbhs`, `near2_curry`, `near2_pair`, `filter_of_nearI`
  + definition `near2E`
  + module `NearNbhs` (with (re)definition `near_simpl` and ltac `near_simpl`)
  + lemma `near_swap`
  + classes `Filter`
  + lemmas `filter_setT`, `filterP_strong`
  + structure `filter_on`
  + definition `filter_class`
  + coercion `filter_filter'`
  + structure `pfilter_on`
  + definition `pfilter_class`
  + canonical `pfilter_filter_on`
  + coercion `pfilter_filter_on`
  + definiton `PFilterType`
  + instances `filter_on_Filter`, `pfilter_on_ProperFilter`
  + lemma `nbhs_filter_onE`, `near_filter_onE`
  + definition and canonical `trivial_filter_on`
  + lemmas `filter_nbhsT`, `nearT`, `filter_not_empty_ex`
  + lemma `filter_ex_subproof`, definition `filter_ex`
  + lemma `filter_getP`
  + record `in_filter`
  + module type `in_filter`, module `PropInFilter`, notation `prop_of`, definition `prop_ofE`,
    notation `_ \is_near _`, definition `is_nearE`
  + lemma `prop_ofP`
  + definition `in_filterT`
  + canonical `in_filterI`
  + lemma `filter_near_of`
  + fact `near_key`
  + lemmas `mark_near`, `near_acc`, `near_skip_subproof`
  + tactic notations `near=>`, `near:`, `near do _`
  + ltacs `just_discharge_near`, `near_skip`, `under_near`, `end_near`, `done`
  + lemmas `have_near`, `near`, `nearW`, `filterE`, `filter_app`, `filter_app2`,
    `filter_app3`, `filterS2`, `filterS3`, `filter_const`, `in_filter_from`,
    `near_andP`, `nearP_dep`, `filter2P`, `filter_ex2`, `filter_fromP`, `filter_fromTP`,
    `filter_from_filter`, `filter_fromT_filter`, `filter_from_proper`, `filter_bigI`,
    `filter_forall`, `filter_imply`
  + definition `fmap`
  + lemma `fmapE`
  + notations `_ @[_ --> _]`, `_ @[_ \oo]`, `_ @ _`, `limn`, `cvgn`
  + instances `fmap_filter`, `fmap_proper_filter`
  + definition `fmapi`, notations `_ `@[_ --> _]`, `_ `@ _`
  + lemma `fmapiE`
  + instances `fmapi_filter`. `fmapi_proper_filter`
  + lemmas `cvg_id`, `fmap_comp`, `appfilter`, `cvg_app`, `cvgi_app`, `cvg_comp`,
    `cvgi_comp`, `near_eq_cvg`, `eq_cvg`, `eq_is_cvg_in`, `eq_is_cvg`, `neari_eq_loc`,
    `cvg_near_const`
  + definition `continuous_at`, notation `continuous`
  + lemma `near_fun`
  + definition `globally`, lemma `globally0`, instances `globally_filter`, `globally_properfilter`
  + definition `frechet_filter`, instances `frechet_properfilter`, `frechet_properfilter_nat`
  + definition `at_point`, instance `at_point_filter`
  + instances `filter_prod_filter`, `filter_prod_proper`, canonical `prod_filter_on`
  + lemmas `filter_prod1`, `filter_prod2`
  + definition `in_filter_prod`
  + lemmas `near_pair`, `cvg_cst`, `cvg_snd`, `near_map`, `near_map2`, `near_mapi`,
    `filter_pair_set`, `filter_pair_near_of`
  + module export `NearMap`
  + lemmas `filterN`, `cvg_pair`, `cvg_comp2`
  + definition `cvg_to_comp_2`
  + definition `within`, lemmas `near_withinE`, `withinT`, `near_withinT`, `cvg_within`,
    `withinET`, instance `within_filter`, canonical `within_filter_on`,
    lemma `filter_bigI_within`
  + definition `subset_filter`, instance `subset_filter_filter`, lemma `subset_filter_proper`
  + definition `powerset_filter_from`, instance `powerset_filter_from_filter`
  + lemmas `near_small_set`, `small_set_sub`, `near_powerset_filter_fromP`,
    `powerset_filter_fromP`, `near_powerset_map`, `near_powerset_map_monoE`
  + definitions `principal_filter`, `principal_filter_type`
  + lemmas `principal_filterP`, `principal_filter_proper`
  + class `UltraFilter`, lemma `ultraFilterLemma`
  + lemmas `filter_image`, `proper_image`, `principal_filter_ultra`, `in_ultra_setVsetC`,
    `ultra_image`
  + instance `smallest_filter_filter`
  + fixpoint `filterI_iter`
  + lemmas `filterI_iter_sub`, `filterI_iterE`
  + definition `finI_from`
  + lemmas `finI_from_cover`, `finI_from1`, `finI_from_countable`, `finI_fromI`,
    `filterI_iter_finI`, `filterI_iter_finI`
  + definition `finI`
  + lemmas `finI_filter`, `filter_finI`, `meets_globallyl`, `meets_globallyr`,
    `meetsxx`, `proper_meetsxx`
  + instance `eventually_filter`, canonicals `eventually_filterType`, `eventually_pfilterType`

- changed when moved from `topology.v` to `filter.v`
  + `Build_ProperFilter` -> `Build_ProperFilter_ex`
  + `ProperFilter'` -> `ProperFilter`
  + remove notation `ProperFilter`

- moved from `topology.v` to `mathcomp_extra.v`:
  + lemma `and_prop_in`
  + lemmas `mem_inc_segment`, `mem_inc_segment`

- moved from `topology.v` to `boolp.v`:
  + lemmas `bigmax_geP`, `bigmax_gtP`, `bigmin_leP`, `bigmin_ltP`

- moved from `topology.v` to `separation_axioms.v`: `set_nbhs`, `set_nbhsP`,
    `accessible_space`, `kolmogorov_space`, `hausdorff_space`,
    `compact_closed`, `discrete_hausdorff`, `compact_cluster_set1`,
    `compact_precompact`, `open_hausdorff`, `hausdorff_accessible`,
    `accessible_closed_set1`, `accessible_kolmogorov`,
    `accessible_finite_set_closed`, `subspace_hausdorff`, `order_hausdorff`,
    `ball_hausdorff`, `Rhausdorff`, `close`, `closeEnbhs`, `closeEonbhs`,
    `close_sym`, `cvg_close`, `close_refl`, `cvgx_close`, `cvgi_close`,
    `cvg_toi_locally_close`, `closeE`, `close_eq`, `cvg_unique`, `cvg_eq`,
    `cvgi_unique`, `close_cvg`, `lim_id`, `lim_near_cst`, `lim_cst`,
    `entourage_close`, `close_trans`, `close_cvgxx`, `cvg_closeP`,
    `ball_close`, `normal_space`, `regular_space`, `compact_regular`,
    `uniform_regular`, `totally_disconnected`, `zero_dimensional`,
    `discrete_zero_dimension`, `zero_dimension_totally_disconnected`,
    `zero_dimensional_ray`, `type`, `countable_uniform_bounded`,
    `countable_uniform`, `sup_pseudometric`, `countable_uniformityT`, `gauge`,
    `iter_split_ent`, `gauge_ent`, `gauge_filter`, `gauge_refl`, `gauge_inv`,
    `gauge_split`, `gauge_countable_uniformity`, `uniform_pseudometric_sup`,
    `perfect_set`, `perfectTP`, and `perfectTP_ex`.

- in `numfun.v`:
  + lemma `gt0_funeposM` renamed to `ge0_funeposM`
    and hypothesis weakened from strict to large inequality
  + lemma `gt0_funenegM` renamed to `ge0_funenegM`
    and hypothesis weakened from strict to large inequality
  + lemma `lt0_funeposM` renamed to `le0_funeposM`
    and hypothesis weakened from strict to large inequality
  + lemma `lt0_funenegM` renamed to `le0_funenegM`
    and hypothesis weakened from strict to large inequality

### Renamed

- in file `topology.v` -> `separation_axioms.v`
  + `totally_disconnected_cvg` -> `zero_dimensional_cvg`.
  + `perfect_set2` -> `perfectTP_ex`

### Generalized

- in `constructive_ereal.v`:
  + lemmas `maxeMr`, `maxeMl`, `mineMr`, `mineMr`:
    hypothesis weakened from strict inequality to large inequality

- in `sequences.v`:
  + lemma `eseries_mkcond`
  + lemma `nneseries_tail_cvg`

- in `exp.v`:
  + lemmas `expR_ge1Dx` and `expeR_ge1Dx` (remove hypothesis)
  + lemma `le_ln1Dx` (weaken hypothesis)

- in `derive.v`:
  + lemma `derivableX`

- in `lebesgue_integral.v`:
  + lemma `integral_setD1_EFin`
  + lemmas `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`
  + lemmas `Rintegral_itv_bndo_bndc`, `Rintegral_itv_obnd_cbnd`

### Deprecated

- in `separation_axioms.v`:
  + definition `cvg_toi_locally_close`

- in `realfun.v`:
  + lemma `lime_sup_ge0`

### Removed

- in `constructive_ereal.v`:
  + notation `lte_spaddr` (deprecated since 0.6)
  + notation `gte_opp` (deprecated since 0.6.0)
  + lemmas `daddooe`, `daddeoo`
  + notations `desum_ninftyP`, `desum_ninfty`, `desum_pinftyP`, `desum_pinfty` (deprecated since 0.6.0)
  + notation `eq_pinftyP` (deprecated since 0.6.0)

- in `topology.v`:
  + notation `[filteredType _ of _]`
  + definition `fmap_proper_filter'`
  + definition `filter_map_proper_filter'`
  + definition `filter_prod_proper'`

- in `normedtype.v`:
  + notation `normmZ` (deprecated since 0.6.0)
  + notation `nbhs_image_ERFin` (deprecated since 0.6.0)
  + notations `ereal_limrM`, `ereal_limMr`, `ereal_limN` (deprecated since 0.6.0)
  + notation `norm_cvgi_map_lim` (deprecated since 0.6.0)
  + notations `ereal_cvgN`, `ereal_is_cvgN`, `ereal_cvgrM`, `ereal_is_cvgrM`,
    `ereal_cvgMr`, `ereal_is_cvgMr`, `ereal_cvgM` (deprecated since 0.6.0)
  + notation `cvg_dist`, lemma `__deprecated__cvg_dist` (deprecated since 0.6.0)
  + notation `cvg_dist2`, lemma `__deprecated__cvg_dist2` (deprecated since 0.6.0)
  + notation `cvg_dist0`, lemma `__deprecated__cvg_dist0` (deprecated since 0.6.0)
  + notation `ler0_addgt0P`, lemma `__deprecated__ler0_addgt0P` (deprecated since 0.6.0)
  + notation `cvg_bounded_real`, lemma `__deprecated__cvg_bounded_real` (deprecated since 0.6.0)
  + notation `linear_continuous0`, lemma `__deprecated__linear_continuous0` (deprecated since 0.6.0)

- in `sequences.v`:
  + notation `nneseries_mkcond` (was deprecated since 0.6.0)
  + notation `squeeze`, lemma `__deprecated__squeeze` (deprecated since 0.6.0)
  + notation `cvgPpinfty`, lemma `__deprecated__cvgPpinfty` (deprecated since 0.6.0)
  + notation `cvgNpinfty`, lemma `__deprecated__cvgNpinfty` (deprecated since 0.6.0)
  + notation `cvgNninfty`, lemma `__deprecated__cvgNninfty` (deprecated since 0.6.0)
  + notation `cvgPninfty`, lemma `__deprecated__cvgPninfty` (deprecated since 0.6.0)
  + notation `ger_cvg_pinfty`, lemma `__deprecated__ger_cvg_pinfty` (deprecated since 0.6.0)
  + notation `ler_cvg_ninfty`, lemma `__deprecated__ler_cvg_ninfty` (deprecated since 0.6.0)
  + notation `lim_ge`, lemma `__deprecated__lim_ge` (deprecated since 0.6.0)
  + notation `lim_le`, lemma `__deprecated__lim_le` (deprecated since 0.6.0)

## [1.4.0] - 2024-09-24

### Added

- in `mathcomp_extra.v`:
  + lemmas `invf_ple`, `invf_lep`

- in `classical_sets.v`:
  + scope `relation_scope` with delimiter `relation`
  + notation `^-1` in `relation_scope` (used to be a local notation)
  + lemma `set_prod_invK` (was a local lemma in `normedtype.v`)
  + definition `diagonal`, lemma `diagonalP`

- in `functions.v`:
  + lemmas `mul_funC`

- in `set_interval.v`:
  + lemma `subset_itvSoo`
  + definitions `itv_is_ray`, `itv_is_bd_open`, and `itv_open_ends`
  + lemmas `itv_open_ends_rside`, `itv_open_ends_rinfty`,
    `itv_open_ends_lside`, `itv_open_ends_linfty`,
    `is_open_itv_itv_is_bd_openP`, `itv_open_endsI`, `itv_setU`,
    `itv_setI`

- in `topology.v`:
  + lemma `filterN`
  + Structures `PointedFiltered`, `PointedNbhs`, `PointedUniform`,
    `PseudoPointedMetric`
  + definition `order_topology`
  + lemmas `discrete_nat`, `rray_open`, `lray_open`, `itv_open`,
    `itv_open_ends_open`, `rray_closed`, `lray_closed`, `itv_closed`,
    `itv_closure`, `itv_closed_infimums`, `itv_closed_supremums`,
    `order_hausdorff`, `clopen_bigcup_clopen`, `zero_dimensional_ray`,
    `order_nbhs_itv`, `open_order_weak`, `real_order_nbhsE`

- in `normedtype.v`:
  + lemmas `not_near_inftyP`, `not_near_ninftyP`
  + lemma `ninftyN`
  + lemma `le_closed_ball`
  + lemmas `nbhs_right_ltW`, `cvg_patch`

- in `derive.v`:
  + lemma `derive_id`
  + lemmas `exp_derive`, `exp_derive1`
  + lemma `derive_cst`
  + lemma `deriveMr`, `deriveMl`

- in `sequences.v`:
  + lemma `cvg_geometric_eseries_half`
  + theorem `Baire`
  + definition `bounded_fun_norm`
  + lemma `bounded_landau`
  + definition `pointwise_bounded`
  + definition `uniform_bounded`
  + theorem `Banach_Steinhauss`

- in `numfun.v`:
  + lemma `indicI`

- in `measure.v`:
  + lemma `measurable_neg`, `measurable_or`

- in `lebesgue_measure.v`:
  + definitions `is_open_itv`, `open_itv_cover`
  + lemmas `outer_measure_open_itv_cover`, `outer_measure_open_le`,
    `outer_measure_open`, `outer_measure_Gdelta`, `negligible_outer_measure`
  + lemmas `measurable_fun_eqr`, `measurable_fun_indic`, `measurable_fun_dirac`,
    `measurable_fun_addn`, `measurable_fun_maxn`, `measurable_fun_subn`,
	`measurable_fun_ltn`, `measurable_fun_leq`, `measurable_fun_eqn`
  + module `NGenCInfty`
    * definition `G`
    * lemmas `measurable_itv_bounded`, `measurableE`

- in `lebesgue_integral.v`:
  + lemma `integralZr`
  + lemma `locally_integrableS`
  + lemma `integrable_locally_restrict`
  + lemma `near_davg`
  + lemma `lebesgue_pt_restrict`

- in `ftc.v`:
  + lemmas `integration_by_parts`, `Rintegration_by_parts`
  + corollary `continuous_FTC1_closed`

### Changed

- in `topology.v`:
  + removed the pointed assumptions from `FilteredType`, `Nbhs`,
    `TopologicalType`, `UniformType`, and `PseudoMetricType`.
  + if you want the original pointed behavior, use the `p` variants
    of the types, so `ptopologicalType` instead of `topologicalType`.
  + generalized most lemmas to no longer depend on pointedness.
    The main exception is for references to `cvg` and `lim` that depend
    on `get` for their definition.
  + `pointed_principal_filter` becomes `principle_filter_type` and
    requires only `choiceType` instead of `pointedType`
  + `pointed_discrete_topology` becomes `discrete_topology_type` and
    requires only `choiceType` instead of `pointedType`
  + renamed lemma `discrete_pointed`to `discrete_space_discrete`

- in `function_space.v`:
  + generalized most lemmas to no longer depend on pointedness.

- in `normedtype.v`:
  + remove superflous parameters in lemmas `not_near_at_rightP` and `not_near_at_leftP`
  + lemma `continuous_within_itvP`: change the statement to use the notation `[/\ _, _ & _]`

- moved from `numfun.v` to `cardinality.v`:
  + lemma `fset_set_comp`

- moved `summability.v` from `theories` to `theories/showcase`

- in `lebesgue_measure.v`:
  + remove redundant hypothesis from lemma `pointwise_almost_uniform`

- moved from `lebesgue_measure.v` to `set_interval.v`: `is_open_itv`, and
    `open_itv_cover`

- in `lebesgue_integral.v`:
  + lemma `nice_lebesgue_differentiation`: change the local integrability hypothesis to
    easy application

- in `ftc.v`:
  + lemma `FTC1_lebesgue_pt`, corollaries `FTC1`, `FTC1Ny`: integrability hypothesis weakened

### Renamed

- in `set_interval.v`:
  + `subset_itvS` -> `subset_itvScc`

- in `topology.v`:
  + in mixin `Nbhs_isUniform_mixin`:
    * `entourage_refl_subproof` -> `entourage_diagonal_subproof`
  + in factory `Nbhs_isUniform`:
    * `entourage_refl` -> `entourage_diagonal`
  + in factory `isUniform`:
    * `entourage_refl` -> `entourage_diagonal`

- in `lebesgue_measure.v`:
  + `measurable_exprn` -> `exprn_measurable`
  + `measurable_mulrl` -> `mulrl_measurable`
  + `measurable_mulrr` -> `mulrr_measurable`
  + `measurable_fun_pow` -> `measurable_funX`
  + `measurable_oppe` -> `oppe_measurable`
  + `measurable_abse` -> `abse_measurable`
  + `measurable_EFin` -> `EFin_measurable`
  + `measurable_oppr` -> `oppr_measurable`
  + `measurable_normr` -> `normr_measurable`
  + `measurable_fine` -> `fine_measurable`
  + `measurable_natmul` -> `natmul_measurable`

- in `lebesgue_integral.v`
  + lemma `integrable_locally` -> `open_integrable_locally`

### Generalized

- in `derive.v`:
  + lemma `derivable_cst`

- in `lebesgue_measure.v`:
  + lemma `measurable_funX` (was `measurable_fun_pow`)

- in `lebesgue_integral.v`
  + lemma `ge0_integral_closed_ball`

- in `ftc.v`:
  + lemma `continuous_FTC2` (continuity hypothesis weakened)

### Removed

- in `lebesgue_measure.v`:
  + notation `measurable_fun_sqr` (was deprecated since 0.6.3)
  + notation `measurable_fun_exprn` (was deprecated since 0.6.3)
  + notation `measurable_funrM` (was deprecated since 0.6.3)
  + notation `emeasurable_fun_minus` (was deprecated since 0.6.3)
  + notation `measurable_fun_abse` (was deprecated since 0.6.3)
  + notation `measurable_fun_EFin` (was deprecated since 0.6.3)
  + notation `measurable_funN` (was deprecated since 0.6.3)
  + notation `measurable_fun_opp` (was deprecated since 0.6.3)
  + notation `measurable_fun_normr` (was deprecated since 0.6.3)
  + notation `measurable_fun_fine` (was deprecated since 0.6.3)
- in `topology.v`:
  + turned into Let's (inside `HB.builders`):
    * lemmas `nbhsE_subproof`, `openE_subproof`
    * lemmas `nbhs_pfilter_subproof`, `nbhsE_subproof`, `openE_subproof`
    * lemmas `open_fromT`, `open_fromI`, `open_from_bigU`
    * lemmas `finI_from_cover`, `finI_from_join`
    * lemmas `nbhs_filter`, `nbhs_singleton`, `nbhs_nbhs`
    * lemmas `ball_le`, `entourage_filter_subproof`, `ball_sym_subproof`,
      `ball_triangle_subproof`, `entourageE_subproof`

## [1.3.1] - 2024-08-09

### Changed

- in `wochoice.v`:
  + two applications of the lemma `in3W` have been removed because they seem to cause
    a universe inconsistency when one loads the `ring` module of `algebra-tactics`

### Generalized

- in `reals.v`:
  + lemma `rat_in_itvoo` (from `realType` to `archiFieldType`)

## [1.3.0] - 2024-08-06

### Added

- in `mathcomp_extra.v`:
  + lemma `ge_floor`
  + lemmas `intr1D`, `intrD1`, `floor_eq`, `floorN`
  + lemma `invf_ltp`

- new file `wochoice.v`:
  + definition `prop_within`
  + lemmas `withinW`, `withinT`, `sub_within`
  + notation `{in <= _, _}`
  + definitions `maximal`, `minimal`, `upper_bound`, `lower_bound`, `preorder`, `partial_order`,
   `total_order`, `nonempty`, `minimum_of`, `maximum_of`, `well_order`, `chain`, `wo_chain`
  + lemmas `antisymmetric_wo_chain`, `antisymmetric_well_order`, `wo_chainW`, `wo_chain_reflexive`,
    `wo_chain_antisymmetric`, `Zorn's_lemma`, `Hausdorff_maximal_principle`, `well_ordering_principle`

- in `classical_sets.v`:
  + lemma `setCD`
  + definition `setY`, notation ``` `+` ```
  + lemmas `setY0`, `set0Y`, `setYK`, `setYC`, `setYA`, `setIYl`, `mulrYr`,
    `setY_def`, `setYE`, `setYU`, `setYI`, `setYD`, `setYCT`, `setCYT`, `setYTC`, `setTYC`
  + lemma `setDU`
  + lemmas `setC_I`, `bigcup_subset`
  + lemmas `xsectionP`, `ysectionP`

- in `constructive_ereal.v`:
  + lemmas `lteD2rE`, `leeD2rE`
  + lemmas `lte_dD2rE`, `lee_dD2rE`

- in `reals.v`:
  + lemma `mem_rg1_floor`

- in `set_interval.v`:
  + lemmas `subset_itvl`, `subset_itvr`, `subset_itvS`
  + lemma `interval_set1`

- in `topology.v`:
  + lemma `ball_subspace_ball`

- in `ereal.v`:
  + lemmas `restrict_EFin`

- in `normedtype.v`:
  + lemmas `nbhs_lt`, `nbhs_le`
  + lemma `nbhs_right_ltDr`

- in `numfun.v`:
  + lemma `epatch_indic`
  + lemma `restrict_normr`
  + lemmas `funepos_le`, `funeneg_le`

- in `realfun.v`:
  + lemma `nondecreasing_at_left_is_cvgr`
  + lemmas `nondecreasing_at_left_at_right`, `nonincreasing_at_left_at_right`

- in `measure.v`:
  + factory `isAlgebraOfSets_setD`
  + defintion `setY_closed`
  + factory `isRingOfSets_setY`
  + definition `completed_measure_extension`
  + lemma `completed_measure_extension_sigma_finite`
  + definition `lim_sup_set`
  + lemmas `lim_sup_set_ub`, `lim_sup_set_cvg`, `lim_sup_set_cvg0`

- in `lebesgue_stieltjes_measure.v`:
  + definition `completed_lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + definition `completed_lebesgue_measure`
  + lemma `completed_lebesgue_measure_is_complete`
  + definition `completed_algebra_gen`
  + lemmas `g_sigma_completed_algebra_genE`, `negligible_sub_caratheodory`,
    `completed_caratheodory_measurable`

- in `lebesgue_integral.v`:
  + lemmas `eq_Rintegral`, `Rintegral_mkcond`, `Rintegral_mkcondr`, `Rintegral_mkcondl`,
    `le_normr_integral`, `Rintegral_setU_EFin`, `Rintegral_set0`, `Rintegral_itv_bndo_bndc`,
    `Rintegral_itv_obnd_cbnd`, `Rintegral_set1`, `Rintegral_itvB`
  + lemma `integral_Sset1`
  + lemma `integralEpatch`
  + lemma `integrable_restrict`
  + lemma `le_integral`
  + lemma `null_set_integral`
  + lemma `EFin_normr_Rintegral`

- in `charge.v`:
  + definition `charge_variation`
  + lemmas `abse_charge_variation`, `charge_variation_continuous`
  + definition `induced`
  + lemmas `semi_sigma_additive_nng_induced`, `dominates_induced`, `integral_normr_continuous`

- in `ftc.v`:
  + lemma `FTC1` (specialization of the previous `FTC1` lemma, now renamed to `FTC1_lebesgue_pt`)
  + lemma `FTC1Ny`
  + definition `parameterized_integral`
  + lemmas `parameterized_integral_near_left`,
    `parameterized_integral_left`, `parameterized_integral_cvg_at_left`,
    `parameterized_integral_continuous`
  + corollary `continuous_FTC2`

### Changed

- in `mathcomp_extra.v`:
  + Notation "f \^-1" now at level 35 with f at next level

- in `classical_sets.v`:
  + lemmas `Zorn` and `ZL_preorder` now require a relation of type `rel T` instead of `T -> T -> Prop`

- moved from `reals.v` to `mathcomp_extra.v`
  + lemma `lt_succ_floor`: conclusion changed to match `lt_succ_floor` in MathComp,
    generalized to `archiDomainType`
  + generalized to `archiDomainType`:
    lemmas `floor_ge0`, `floor_lt0`, `floor_natz`,
    `floor_ge_int`, `floor_neq0`, `floor_lt_int`, `ceil_ge`, `ceil_ge0`, `ceil_gt0`,
    `ceil_le0`, `ceil_ge_int`, `ceilN`, `abs_ceil_ge`
  + generalized to `archiDomainType` and precondition generalized:
    * `floor_le0`
  + generalized to `archiDomainType` and renamed:
    * `ceil_lt_int` -> `ceil_gt_int`

- in `reals.v`:
  + definitions `Rceil`, `Rfloor`

- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in `lebesgue_integral.v`:
  + lemma `measurable_int`: argument `mu` now explicit

- moved from `lebesgue_integral.v` to `ereal.v`:
  + lemma `funID`

- moved from `lebesgue_integral.v` to `numfun.v`:
  + lemmas `fimfunEord`, `fset_set_comp`

- moved from `lebesgue_integral.v` to `cardinality.v`:
  + hint `solve [apply: fimfunP]`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pdivr_mull` -> `lte_pdivrMl`
  + `lte_pdivr_mulr` -> `lte_pdivrMr`
  + `lte_pdivl_mull` -> `lte_pdivlMl`
  + `lte_pdivl_mulr` -> `lte_pdivlMr`
  + `lte_ndivl_mulr` -> `lte_ndivlMr`
  + `lte_ndivl_mull` -> `lte_ndivlMl`
  + `lte_ndivr_mull` -> `lte_ndivrMl`
  + `lte_ndivr_mulr` -> `lte_ndivrMr`
  + `lee_pdivr_mull` -> `lee_pdivrMl`
  + `lee_pdivr_mulr` -> `lee_pdivrMr`
  + `lee_pdivl_mull` -> `lee_pdivlMl`
  + `lee_pdivl_mulr` -> `lee_pdivlMr`
  + `lee_ndivl_mulr` -> `lee_ndivlMr`
  + `lee_ndivl_mull` -> `lee_ndivlMl`
  + `lee_ndivr_mull` -> `lee_ndivrMl`
  + `lee_ndivr_mulr` -> `lee_ndivrMr`
  + `eqe_pdivr_mull` -> `eqe_pdivrMl`
  + `lte_dadd` -> `lte_dD`
  + `lee_daddl` -> `lee_dDl`
  + `lee_daddr` -> `lee_dDr`
  + `gee_daddl` -> `gee_dDl`
  + `gee_daddr` -> `gee_dDr`
  + `lte_daddl` -> `lte_dDl`
  + `lte_daddr` -> `lte_dDr`
  + `gte_dsubl` -> `gte_dBl`
  + `gte_dsubr` -> `gte_dBr`
  + `gte_daddl` -> `gte_dDl`
  + `gte_daddr` -> `gte_dDr`
  + `lee_dadd2lE` -> `lee_dD2lE`
  + `lte_dadd2lE` -> `lte_dD2lE`
  + `lee_dadd2rE` -> `lee_dD2rE`
  + `lee_dadd2l` -> `lee_dD2l`
  + `lee_dadd2r` -> `lee_dD2r`
  + `lee_dadd` -> `lee_dD`
  + `lee_dsub` -> `lee_dB`
  + `lte_dsubl_addr` -> `lte_dBlDr`
  + `lte_dsubl_addl` -> `lte_dBlDl`
  + `lte_dsubr_addr` -> `lte_dBrDr`
  + `lte_dsubr_addl` -> `lte_dBrDl`
  + `gte_opp` -> `gteN`
  + `gte_dopp` -> `gte_dN`
  + `lte_le_add` -> `lte_leD`
  + `lee_lt_add` -> `lee_ltD`
  + `lte_le_dadd` -> `lte_le_dD`
  + `lee_lt_dadd` -> `lee_lt_dD`
  + `lte_le_sub` -> `lte_leB`
  + `lte_le_dsub` -> `lte_le_dB`

- in `classical_sets.v`:
  + `setM` -> `setX`
  + `in_setM` -> `in_setX`
  + `setMR` -> `setXR`
  + `setML` -> `setXL`
  + `setM0` -> `setX0`
  + `set0M` -> `set0X`
  + `setMTT` -> `setXTT`
  + `setMT` -> `setXT`
  + `setTM` -> `setTX`
  + `setMI` -> `setXI`
  + `setM_bigcupr` -> `setX_bigcupr`
  + `setM_bigcupl` -> `setX_bigcupl`
  + `bigcup_setM_dep` -> `bigcup_setX_dep`
  + `bigcup_setM` -> `bigcup_setX`
  + `fst_setM` -> `fst_setX`
  + `snd_setM` -> `snd_setX`
  + `in_xsectionM` -> `in_xsectionX`
  + `in_ysectionM` -> `in_ysectionX`
  + `notin_xsectionM` -> `notin_xsectionX`
  + `notin_ysectionM` -> `notin_ysectionX`
  + `setSM` -> `setSX`
  + `bigcupM1l` -> `bigcupX1l`
  + `bigcupM1r` -> `bigcupX1r`

- in `cardinality.v`:
  + `countableMR` -> `countableXR`
  + `countableM` -> `countableX`
  + `countableML` -> `countableXL`
  + `infiniteMRl` -> `infiniteXRl`
  + `cardMR_eq_nat` -> `cardXR_eq_nat`
  + `finite_setM` -> `finite_setX`
  + `finite_setMR` -> `finite_setXR`
  + `finite_setML` -> `finite_setXL`
  + `fset_setM` -> `fset_setX`

- in `reals.v`:
  + `inf_lb` -> `inf_lbound`
  + `sup_ub` -> `sup_ubound`
  + `ereal_inf_lb` -> `ereal_inf_lbound`
  + `ereal_sup_ub` -> `ereal_sup_ubound`

- in `topology.v`:
  + `compact_setM` -> `compact_setX`

- in `measure.v`:
  + `measurable_restrict` -> `measurable_restrictT`
  + `setD_closed` -> `setSD_closed`
  + `measurableM` -> `measurableX`

- in `ftc.v`:
  + `FTC1` -> `FTC1_lebesgue_pt`

### Generalized

- in `constructive_ereal.v`:
  + lemmas `leeN2`, `lteN2` generalized from `realDomainType` to `numDomainType`

- in `measure.v`:
  + lemma `measurable_restrict`

### Deprecated

- in `constructive_ereal.v`:
  + lemmas `lte_opp2`, `lee_opp2` (use `lteN2`, `leeN2` instead)

- in `reals.v`:
  + `floor_le` (use `ge_floor` instead)
  + `le_floor` (use `Num.Theory.floor_le` instead)
  + `le_ceil` (use `ceil_ge` instead)

- in `lebesgue_integral.v`:
  + lemmas `integralEindic`, `integral_setI_indic`

### Removed

- in `classical_sets.v`:
  + inductive `tower`
  + lemma `ZL'`

- in `reals.v`:
  + definition `floor` (use `Num.floor` instead)
  + definition `ceil` (use `Num.ceil` instead)
  + lemmas `floor0`, `floor1`
  + lemma `le_floor` (use `Num.Theory.floor_le` instead)

- in `topology.v`, `function_spaces.v`, `normedtype.v`:
  + local notation `to_set`

## [1.2.0] - 2024-06-06

### Added

- in file `mathcomp_extra.v`:
  + module `Order`
    * definitions `disp_t`, `default_display`
  + lemma `Pos_to_natE`

- in `classical_sets.v`:
  + lemma `bigcup_recl`
  + notations `\bigcup_(i >= n) F i` and `\bigcap_(i >= n) F i`
  + lemmas `bigcup_addn`, `bigcap_addn`
  + lemmas `setD_bigcup`, `nat_nonempty`
  + hint `nat_nonempty`
  + lemma `bigcup_bigsetU_bigcup`
  + lemmas `setDUD`, `setIDAC`

- in `Rstruct.v`:
  + lemma `IZRposE`

- in `signed.v`:
  + lemma `onem_nonneg_proof`, definition `onem_nonneg`

- in `esum.v`:
  + lemma `nneseries_sum_bigcup`

- in `normedtype.v`:
  + lemma `not_near_at_leftP`

- in `sequences.v`:
  + lemma `nneseries_recl`
  + lemma `nneseries_addn`

- in `realfun.v`
  + lemmas `total_variation_nondecreasing`, `total_variation_bounded_variation`

- in `measure.v`:
  + definition `subset_sigma_subadditive`
  + factory `isSubsetOuterMeasure`
  + structure `SigmaRing`, notation `sigmaRingType`
  + factory `isSigmaRing`
  + lemma `bigcap_measurable` for `sigmaRingType`
  + lemma `setDI_semi_setD_closed`
  + lemmas `powerset_lambda_system`, `lambda_system_smallest`, `sigmaRingType_lambda_system`
  + definitions `niseq_closed`, `sigma_ring` (notation `<<sr _ >>`),
    `monotone` (notation `<<M _ >>`)
  + lemmas `smallest_sigma_ring`, `sigma_ring_monotone`, `g_sigma_ring_monotone`,
    `sub_g_sigma_ring`, `setring_monotone_sigma_ring`, `g_monotone_monotone`,
	`g_monotone_setring`, `g_monotone_g_sigma_ring`, `monotone_setring_sub_g_sigma_ring`
  + lemmas `powerset_sigma_ring`, `g_sigma_ring_strace`, `setI_g_sigma_ring`,
    `subset_strace`
  + lemma `measurable_and`
  + lemma `measurableID`
  + lemma `strace_sigma_ring`

- in `lebesgue_measure.v`:
  + lemma `measurable_fun_ler`
  + lemmas `measurable_natmul`, `measurable_fun_pow`

- in `lebesgue_integral.v`:
  + lemmas `integrableMl`, `integrableMr`

- in `probability.v`:
  + definition `bernoulli_pmf`
  + lemmas `bernoulli_pmf_ge0`, `bernoulli_pmf1`, `measurable_bernoulli_pmf`
  + definition  `bernoulli` (equipped with the `probability` structure)
  + lemmas `bernoulli_dirac`, `bernoulliE`, `integral_bernoulli`, `measurable_bernoulli`,
    `measurable_bernoulli2`
  + definition `binomial_pmf`
  + lemmas `binomial_pmf_ge0`, `measurable_binomial_pmf`
  + definitions `binomial_prob` (equipped with the `probability` structure), `bin_prob`
  + lemmas `bin_prob0`, `bin_prob1`, `binomial_msum`, `binomial_probE`, `integral_binomial`,
    `integral_binomial_prob`, `measurable_binomial_prob`
  + definition `uniform_pdf`
  + lemmas `measurable_uniform_pdf`, `integral_uniform_pdf`, `integral_uniform_pdf1`
  + definition `uniform_prob` (equipped with the `probability` structure)
  + lemmas `dominates_uniform_prob`, `integral_uniform`

- new file `theories/all_analysis.v`

### Changed

- in `forms.v`:
  + notation ``` u ``_ _ ```

- in `sequences.v`:
  + definition `expR` is now HB.locked
  + equality reversed in lemma `eq_bigcup_seqD`
  + `eq_bigsetU_seqD` renamed to `nondecreasing_bigsetU_seqD`
    and equality reversed

- in `trigo.v`:
  + definitions `sin`, `cos`, `acos`, `asin`, `atan` are now HB.locked

- in `measure.v`:
  + change the hypothesis of `measurable_fun_bool`
  + mixin `AlgebraOfSets_isMeasurable` renamed to `hasMeasurableCountableUnion`
    and made to inherit from `SemiRingOfSets`
  + rm hypo and variable in lemma `smallest_monotone_classE`
    and rename to `smallest_lambda_system`
  + rm hypo in lemma `monotone_class_g_salgebra` and renamed
    to `g_salgebra_lambda_system`
  + rm hypo in lemma `monotone_class_subset` and renamed to
    `lambda_system_subset`
  + notation `<<m _, _>>` changed to `<<l _, _>>`,
    notation `<<m _>>` changed to `<<l _>>`

- moved from `lebesgue_measure.v` to `measure.v`:
  + definition `strace`
  + lemma `sigma_algebra_strace`

### Renamed

- in `classical_sets.v`:
  + `notin_set` -> `notin_setE`

- in `constructive_ereal.v`:
  + `gee_pmull` -> `gee_pMl`
  + `gee_addl` -> `geeDl`
  + `gee_addr` -> `geeDr`
  + `gte_addl` -> `gteDl`
  + `gte_addr` -> `gteDr`
  + `lte_subl_addr` -> `lteBlDr`
  + `lte_subl_addl` -> `lteBlDl`
  + `lte_subr_addr` -> `lteBrDr`
  + `lte_subr_addl` -> `lteBrDl`
  + `lee_subl_addr` -> `leeBlDr`
  + `lee_subl_addl` -> `leeBlDl`
  + `lee_subr_addr` -> `leeBrDr`
  + `lee_subr_addl` -> `leeBrDl`
  + `num_lee_maxr` -> `num_lee_max`
  + `num_lee_maxl` -> `num_gee_max`
  + `num_lee_minr` -> `num_lee_min`
  + `num_lee_minl` -> `num_gee_min`
  + `num_lte_maxr` -> `num_lte_max`
  + `num_lte_maxl` -> `num_gte_max`
  + `num_lte_minr` -> `num_lte_min`
  + `num_lte_minl` -> `num_gte_min`

- in `signed.v`:
  + `num_le_maxr` -> `num_le_max`
  + `num_le_maxl` -> `num_ge_max`
  + `num_le_minr` -> `num_le_min`
  + `num_le_minl` -> `num_ge_min`
  + `num_lt_maxr` -> `num_lt_max`
  + `num_lt_maxl` -> `num_gt_max`
  + `num_lt_minr` -> `num_lt_min`
  + `num_lt_minl` -> `num_gt_min`

- in `measure.v`:
  + `sub_additive` -> `subadditive`
  + `sigma_sub_additive` -> `measurable_subset_sigma_subadditive`
  + `content_sub_additive` -> `content_subadditive`
  + `ring_sigma_sub_additive` -> `ring_sigma_subadditive`
  + `Content_SubSigmaAdditive_isMeasure` -> `Content_SigmaSubAdditive_isMeasure`
  + `measure_sigma_sub_additive` -> `measure_sigma_subadditive`
  + `measure_sigma_sub_additive_tail` -> `measure_sigma_subadditive_tail`
  + `bigcap_measurable` -> `bigcap_measurableType`
  + `monotone_class` -> `lambda_system`
  + `monotone_class_g_salgebra` -> `g_sigma_algebra_lambda_system`
  + `smallest_monotone_classE` -> `smallest_lambda_system`
  + `dynkin_monotone` -> `dynkin_lambda_system`
  + `dynkin_g_dynkin` -> `g_dynkin_dynkin`
  + `salgebraType` -> `g_sigma_algebraType`
  + `g_salgebra_measure_unique_trace` -> `g_sigma_algebra_measure_unique_trace`
  + `g_salgebra_measure_unique_cover` -> `g_sigma_algebra_measure_unique_cover`
  + `g_salgebra_measure_unique` -> `g_sigma_algebra_measure_unique`
  + `setI_closed_gdynkin_salgebra` -> `setI_closed_g_dynkin_g_sigma_algebra`

- in `lebesgue_integral.v`:
  + `integral_measure_add` -> `ge0_integral_measure_add`
  + `integral_pushforward` -> `ge0_integral_pushforward`

### Generalized

- in `Rstruct.v`:
  + lemmas `RinvE`, `RdivE`

- in `constructive_ereal.v`:
  + `gee_pMl` (was `gee_pmull`)

- in `sequences.v`:
  + lemmas `eseries0`, `nneseries_split`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2` (from `semiRingOfSetType` to `Type`)
  + lemmas `caratheodory_measurable_mu_ext`, `measurableM`, `measure_dominates_trans`, `ess_sup_ge0`
    definitions `preimage_classes`, `measure_dominates`, `ess_sup`
	(from `measurableType` to `semiRingOfSetsType`)
  + lemmas ` measurable_prod_measurableType`, `measurable_prod_g_measurableTypeR` (from `measurableType` to `algebraOfSetsType`)
  + from `measurableType` to `sigmaRingType`
    * lemmas `bigcup_measurable`, `bigcapT_measurable`
	* definition `measurable_fun`
	* lemmas `measurable_id`, `measurable_comp`, `eq_measurable_fun`, `measurable_cst`,
	  `measurable_fun_bigcup`, `measurable_funU`, `measurable_funS`, `measurable_fun_if`
	* lemmas `semi_sigma_additiveE`, `sigma_additive_is_additive`, `measure_sigma_additive`
	* definitions `pushforward`, `dirac`
	* lemmas `diracE`, `dirac0`, `diracT`, `finite_card_sum`, `finite_card_dirac`, `infinite_card_dirac`
	* definitions `msum`, `measure_add`, `mscale`, `mseries`, `mrestr`
	* lemmas `msum_mzero`, `measure_addE`
	* definition `sfinite_measure`
	* mixin `isSFinite`, structure `SFiniteMeasure`
	* structure `FiniteMeasure`
	* factory `Measure_isSFinite`
	* lemma `negligible_bigcup`
	* definition `ae_eq`
	* lemmas `ae_eq0`, `ae_eq_comp`, `ae_eq_funeposneg`, `ae_eq_refl`, `ae_eq_sym`,
	  `ae_eq_trans`, `ae_eq_sub`, `ae_eq_mul2r`, `ae_eq_mul2l`, `ae_eq_mul1l`,
	  `ae_eq_abse`, `ae_eq_subset`
  + from `measurableType` to `sigmaRingType` and from `realType` to `realFieldType`
	* definition `mzero`
  + from `realType` to `realFieldType`:
    * lemma `sigma_finite_mzero`

- in `lebesgue_measure.v`:
  + from `measurableType` to `sigmaRingType`
    * section `measurable_fun_measurable`

- in `lebesgue_integral.v`:
  + lemma `ge0_integral_bigcup`
  + lemma `ge0_emeasurable_fun_sum`
  + from `measurableType` to `sigmaRingType`
    * mixin `isMeasurableFun`
    * structure `SimpleFun`
	* structure `NonNegSimpleFun`
	* sections `fimfun_bin`, `mfun_pred`, `sfun_pred`, `simple_bounded`
	* lemmas `nnfun_muleindic_ge0`, `mulemu_ge0`, `nnsfun_mulemu_ge0`
	* section `sintegral_lemmas`
	* lemma `eq_sintegral`
	* section `sintegralrM`

- in `probability.v`:
  + lemma `markov`

### Deprecated

- in `classical_sets.v`:
  + `notin_set` (use `notin_setE` instead)

### Removed

- in `forms.v`
  + canonical `rev_mulmx`
  + structure `revop`

- in `reals.v`
  + lemma `inf_lower_bound` (use `inf_lb` instead)

- in `derive.v`:
  + definition `mulr_rev`
  + canonical `rev_mulr`
  + lemmas `mulr_is_linear`, `mulr_rev_is_linear`

- in `measure.v`:
  + lemmas `prod_salgebra_set0`, `prod_salgebra_setC`, `prod_salgebra_bigcup`
    (use `measurable0`, `measurableC`, `measurable_bigcup` instead)

- in `lebesgue_measure.v`:
  + lemmas `stracexx`, `strace_measurable`

- in `lebesgue_integral.v`:
  + `integrablerM`, `integrableMr` (were deprecated since version 0.6.4)

## [1.1.0] - 2024-03-31

### Added

- in `mathcomp_extra.v`
  + lemma `invf_plt`

- in `contra.v`:
  + in module `Internals`
    * variant `equivT`
    * definitions `equivT_refl`, `equivT_transl`, `equivT_sym`, `equivT_trans`,
      `equivT_transr`, `equivT_Prop`, `equivT_LR` (hint view), `equivT_RL` (hint view)
  + definition `notP`
  + hint view for `move/` and `apply/` for `Internals.equivT_LR`, `Internals.equivT_RL`

- in `set_interval.v`
  + lemmas `setDitv1r`, `setDitv1l`
  + lemmas `set_itvxx`, `itv_bndbnd_setU`

- in `reals.v`
  + lemma `abs_ceil_ge`

- in `topology.v`:
  + lemmas `nbhs_infty_ger`, `nbhs0_ltW`, `nbhs0_lt`

- file `function_spaces.v`

- in `normedtype.v`
  + lemma `closed_ball_ball`
  + lemma `ball_open_nbhs`
  + definition `completely_regular_space`
  + lemmas `point_uniform_separator`, and
    `uniform_completely_regular`.

- in `exp.v`
  + lemma `ln_lt0`
  + lemma `expRM_natr`

- in `numfun.v`
  + lemma `cvg_indic`

- in `lebesgue_integral.v`
  + lemma `ge0_integralZr`
  + lemma `locally_integrable_indic`
  + definition `davg`,
    lemmas `davg0`, `davg_ge0`, `davgD`, `continuous_cvg_davg`
  + definition `lim_sup_davg`,
    lemmas `lim_sup_davg_ge0`, `lim_sup_davg_le`,
	`continuous_lim_sup_davg`, `lim_sup_davgB`, `lim_sup_davgT_HL_maximal`
  + definition `lebesgue_pt`,
    lemma `continuous_lebesgue_pt`
  + lemma `integral_setU_EFin`
  + lemmas `integral_set1`, `ge0_integral_closed_ball`, `integral_setD1_EFin`,
    `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`
  + lemma `lebesgue_differentiation`
  + lemma `lebesgue_density`
  + definition `nicely_shrinking`,
    lemmas `nicely_shrinking_gt0`, `nicely_shrinking_lty`, `nice_lebesgue_differentiation`

- new file `ftc.v`:
  - lemmas `FTC1`, `continuous_FTC1`

### Changed

- moved from `topology.v` to `function_spaces.v`: `prod_topology`,
    `product_topology_def`, `proj_continuous`, `dfwith_continuous`,
    `proj_open`, `hausdorff_product`, `tychonoff`, `perfect_prod`,
    `perfect_diagonal`, `zero_dimension_prod`, `totally_disconnected_prod`,
    `separate_points_from_closed`, `weak_sep_cvg`, `weak_sep_nbhsE`,
    `weak_sep_openE`, `join_product`, `join_product_continuous`,
    `join_product_open`, `join_product_inj`, `join_product_weak`, `fct_ent`,
    `fct_ent_filter`, `fct_ent_refl`, `fct_ent_inv`, `fct_ent_split`,
    `cvg_fct_entourageP`, `fun_complete`, `fct_ball`, `fct_ball_center`,
    `fct_ball_sym`, `fct_ball_triangle`, `fct_entourage`, `cvg_switch_1`,
    `cvg_switch_2`, `cvg_switch`, `uniform_fun`, `uniform_nbhs`,
    `uniform_entourage`, `restricted_cvgE`, `pointwise_cvgE`,
    `uniform_fun_family`, `uniform_set1`, `uniform_subset_nbhs`,
    `uniform_subset_cvg`, `pointwise_uniform_cvg`, `cvg_sigL`, `eq_in_close`,
    `hausdorrf_close_eq_in`, `uniform_restrict_cvg`, `uniform_nbhsT`,
    `cvg_uniformU`, `cvg_uniform_set0`, `fam_cvgP`, `family_cvg_subset`,
    `family_cvg_finite_covers`, `fam_cvgE`, `fam_nbhs`, `fam_compact_nbhs`,
    `compact_open`, `compact_openK`, `compact_openK_nbhs`,
    `compact_open_of_nbhs`, `compact_open_def`, `compact_open_cvgP`,
    `compact_open_open`, `compact_open_fam_compactP`, `compactly_in`,
    `compact_cvg_within_compact`, `uniform_limit_continuous`,
    `uniform_limit_continuous_subspace`, `singletons`,
    `pointwise_cvg_family_singleton`, `pointwise_cvg_compact_family`,
    `pointwise_cvgP`, `equicontinuous`, `equicontinuous_subset`,
    `equicontinuous_subset_id`, `equicontinuous_continuous_for`,
    `equicontinuous_continuous`, `pointwise_precompact`,
    `pointwise_precompact_subset`, `pointwise_precompact_precompact`,
    `uniform_pointwise_compact`, `precompact_pointwise_precompact`,
    `pointwise_cvg_entourage`, `equicontinuous_closure`, `small_ent_sub`,
    `pointwise_compact_cvg`, `pointwise_compact_closure`,
    `pointwise_precompact_equicontinuous`, `compact_equicontinuous`,
    `precompact_equicontinuous`, `Ascoli`, `continuous_curry`,
    `continuous_uncurry_regular`, `continuous_uncurry`, `curry_continuous`, and
    `uncurry_continuous`.

- moved from `cantor.v` to `topology.v`:
  + lemma `discrete_bool_compact`
  + definition `pointed_principal_filter`
  + definition `pointed_discrete_topology`
  + lemma `discrete_pointed`

- in `measure.v`:
  + lemma `sigma_finiteP` generalized to an equivalence and changed to use `[/\ ..., .. & ....]`

- move from `kernel.v` to `measure.v`
  + definition `mset`, `pset`, `pprobability`
  + lemmas `lt0_mset`, `gt1_mset`

### Renamed

- in `constructive_ereal.v`:
  + `lee_addl` -> `leeDl`
  + `lee_addr` -> `leeDr`
  + `lee_add2l` -> `leeD2l`
  + `lee_add2r` -> `leeD2r`
  + `lee_add` -> `leeD`
  + `lee_sub` -> `leeB`
  + `lee_add2lE` -> `leeD2lE`
  + `lte_add2lE` -> `lteD2lE`
  + `lee_oppl` -> `leeNl`
  + `lee_oppr` -> `leeNr`
  + `lte_oppr` -> `lteNr`
  + `lte_oppl` -> `lteNl`
  + `lte_add` -> `lteD`
  + `lte_addl` -> `lteDl`
  + `lte_addr` -> `lteDr`

- in `exp.v`:
  + `expRMm` -> `expRM_natl`

- in `measure.v`:
  + `Measure_isSFinite_subdef` -> `isSFinite`
  + `sfinite_measure_subdef` -> `s_finite`
  + `SigmaFinite_isFinite` -> `isFinite`
  + `FiniteMeasure_isSubProbability` -> `isSubProbability`

- in `lebesgue_integral.v`
  + `integral_setU` -> `ge0_integral_setU`
  + `subset_integral` -> `ge0_subset_integral`

### Generalized

- in `realfun.v`
  + lemma `lime_sup_le`

### Removed

- in `topology.v`:
  + definition `pointwise_fun`
  + module `PtwsFun`

- in `mathcomp_extra.v`:
  + notations `eqLHS` and `eqRHS`
    (they are `eqbLHS` and `eqbRHS` in mathcomp since 1.15.0)

## [1.0.0] - 2024-01-26

### Added

- in `constructive_ereal.v`:
  + definition `dEFin`
  + notations `%:dE`, `%:E` (`ereal_dual_scope`)
  + notation `\bar^d ...` (`type_scope`) for dual extended real numbers
  + instance using `isNmodule.Build` for `\bar`
  + instances using `Choice.on` and `isNmodule.Build` for `\bar^d`
  + lemma `EFin_semi_additive`
  + lemmas `dEFinE`, `dEFin_semi_additive`
  + instance using `isSemiAdditive.Build` for `\bar^d`
  + canonical `dEFin_snum`

- in `reals.v`:
  + definition `Rint_pred`

- in `topology.v`
  + definition `set_system`, identity coercion `set_system_to_set`
    with instances using `Equality.on`, `Choice.on`, `Pointed.on`,
	`isFiltered.Build`
  + mixin `selfFiltered`, factory `hasNbhs`, structure `Nbhs`,
    type `nbhsType`
  + instance for matrices using `selfFiltered.Build`
  + lemmas `cvg_in_ex`, `cvg_inP`, `cvg_in_toP`, `dvg_inP`, `cvg_inNpoint`,
    `eq_is_cvg_in`
  + notations `E @[ x \oo ]`, `limn`, `cvgn`
  + definition `continuous_at`
  + definitions `weak_topology`, `sup_topology`, `prod_topology`
  + definition `prod_topo_apply`
  + definition `discrete_topology`
  + instead of `zmodType` using `isPointed.Build`
  + definition `pointwise_cvgE`,
    instance using `Uniform.copy` for `{ptws _ -> _}`
  + definition `compact_open_of_nbhs`, lemmas `compact_openK_nbhsE_subproof`,
    `compact_openK_openE_subproof`

- in `cantor.v`:
  + definition `pointed_principal_filter`, instances using `Pointed.on` and `hasNbhs.Build`
  + definition `pointed_discrete_topology`
  + lemma `discrete_pointed`
  + lemma `discrete_bool_compact`

- in `normedtype.v`:
  + definition `urysohnType` with instances using `Pointed.on` and `isUniform.Build`

- in `derive.v`:
  + lemma `cvg_at_rightE`, `cvg_at_leftE`

- in `convex.v`:
  + definition `convex_lmodType` with instances using `Choice.on` and `isConvexSpace.Build`
  + definition `convex_realDomainType` with instance using `isConvexSpace.Build`

- in `lebesgue_stieltjes_measure.v`:
  + instance on `ocitv_type` using `Pointed.on`

- in `lebesgue_integral.v`:
  + mixin `isNonNegFun`, notations `{nnfun _ >-> _}`, `[nnfun of _]`
  + section `ring`
    * lemmas `fimfun_mulr_closed`, instances using `GRing.isMulClosed.Build`,
      `[SubZmodule_isSubRing of ... by <:]`
    * lemmas `fimfunM`, `fimfun1`, `fimfun_prod`, `fimfunX`,
    * lemma `indic_fimfun_subproof`, instance using `indic_fimfun_subproof`
    * definition `indic_fimfun`
    * instance using `FImFun.copy`, definition `scale_fimfun`
  + section `comring`
    * instance using `[SubRing_isSubComRing of ... by <:]`
	* instance using `FImFun.copy`
  + lemmas `fimfunE`, `fimfunEord`, `trivIset_preimage1`, `trivIset_preimage1_in`
  + section `fimfun_bin`
    * lemma `max_fimfun_subproof`, instance using `max_fimfun_subproof`
  + factory `FiniteDecomp`

- in `charge.v`:
  + `cscale` instances using `SigmaFinite_isFinite.Build` and `isAdditiveCharge.Build`

### Changed

- in `boolp.v`:
  + in lemma `gen_choiceMixin`: `Choice.mixin_of` -> `hasChoice`
  + in definition `gen_eqMixin`: `EqMixin` -> `hasDecEq.Build`
  + canonical `dep_arrow_eqType` -> instance using `gen_eqMixin`
  + canonical `dep_arrow_choiceType` -> instance using `gen_choiceMixin`
  + canonical `Prop_eqType` -> instance using `gen_eqMixin`
  + canonical `Prop_choiceType` -> instance using `gen_choiceMixin`
  + canonical `classicType_eqType` -> instance using `gen_eqMixin`
  + canonical `classicType_choiceType` -> instance using `gen_choiceMixin`
  + canonical `eclassicType_eqType` -> instance using `Equality.copy`
  + canonical `eclassicType_choiceType` -> instance using `gen_choiceMixin`
  + definition `porderMixin` and canonical `porderType` -> instance using `isPOrder.Build`
  + definition `latticeMixin` and canonical `latticeType` -> instance using `POrder_isLattice.Build`

- in `classical_sets.v`:
  + canonicals
    `setU_monoid`, `setU_comoid`, `setU_mul_monoid`, `setI_monoid`,
    `setI_comoid`, `setI_mul_monoid`, `setU_add_monoid`, `setI_add_monoid`
	-> instances using
	`isComLaw.Build`, `isMulLaw.Build`, `isComLaw.Build`, `isMulLaw.Build`, `isAddLaw.Build`, `isAddLaw.Build`
  + module `Pointed` (packed class) -> mixin `isPointed`, structure `Pointed`
  + canonical `arrow_pointedType` and definition `dep_arrow_pointedType` -> instance using `isPointed.Build`
  + canonicals
    `unit_pointedType`, `bool_pointedType`, `Prop_pointedType`, `nat_pointedType`,
	`prod_pointedType`, `matrix_pointedType`, `option_pointedType`, `pointed_fset`
	-> instances using
	`isPointed.Build`
  + module `Empty` (packed class) -> mixin `isEmpty`, structure `Empty`, factories `Choice_isEmpty`, `Type_isEmpty`
  + definition `False_emptyMixin` and canonicals `False_eqType`,
    `False_choiceType`, `False_countType`, `False_finType`, `False_emptyType` ->
    instance using `Type_isEmpty.Build`
  + definition `void_emptyMixin` and canonical `void_emptyType` -> instance using `isEmpty.Build`
  + definition `orderMixin` and canonicals `porderType`, `latticeType`, `distrLatticeType` ->
    instances using `Choice.copy` and `isMeetJoinDistrLattice.Build`
  + canonicals `bLatticeType`, `tbLatticeType`, `bDistrLatticeType`, `tbDistrLatticeType` ->
    instances using `hasBottom.Build` and `hasTop.Build`
  + canonical `cbDistrLatticeType` -> instance using `hasRelativeComplement.Build`
  + canonical `ctbDistrLatticeType` -> instance using `hasComplement.Build`

- in `functions.v`:
  + notation `split`
  + notation `\_` moved from `fun_scope` to `function_scope`
  + notations `pinv`, `pPbij`, `pPinj`, `injpPfun`, `funpPinj`
  + in definition `fct_zmodMixin`: `ZmodMixin` -> `isZmodule.Build`
  + canonical `fct_zmodType` -> instance using `fct_zmodMixin`
  + in definition `fct_ringMixin`: `RingMixin` -> `Zmodule_isRing.Build`
  + canonical `fct_ringType` -> instance using `fct_ringMixin`
  + canonical `fct_comRingType` ->
    definition and instance using `Ring_hasCommutativeMul.Build` and `fct_comRingType`
  + definition `fct_lmodMixin` and canonical `fct_lmodType` ->
    definition `fct_lmodMixin` and instance using `fct_lmodMixin`

- in `cardinality.v`:
  + canonical `rat_pointedType` -> instance using `isPointed.Build`
  + canonical `fimfun_subType` -> instance using `isSub.Build`
  + definition `fimfuneqMixin` and canonical `fimfuneqType` -> instance using `[Equality of ... by <:]`
  + definition `fimfunchoiceMixin` and canonical `fimfunchoiceType` -> instance using `[Choice of ... by <:]`
  + canonicals `fimfun_add`, `fimfun_zmod`, `fimfun_zmodType`, and definition `fimfun_zmodMixin` ->
    instances using `isZmodClosed.Build` and `[SubChoice_isSubZmodule of ... <:]`

- in `signed.v`:
  + definitions `signed_subType`, `signed_choiceMixin`, `signed_porderMixin`, 
    canonicals `signed_eqMixin`, `signed_eqType`, `signed_choiceType`, `signed_porderType`
	-> instances using `[isSub for ...]` and `[POrder of ... by <:]`
  + in lemma `signed_le_total`: `totalPOrderMixin` -> `total`
  + canonicals `signed_latticeType`, `signed_distrLatticeType`, `signed_orderType`
    -> instance using `Order.POrder_isTotal.Build`

- in `constructive_ereal.v`:
  + definition `ereal_eqMixin` and canonical `ereal_eqType` -> instance using `hasDecEq.Build`
  + definition `ereal_choiceMixin` and canonical `ereal_choiceType` -> instance using `Choice.copy`
  + definition `ereal_countMixin` and `ereal_countType` -> instance using `PCanIsCountable`
  + definition `ereal_porderMixin` and canonical `Choice.copy` -> instance using `isPOrder.Build`
  + in lemma `le_total_ereal` : `le_total_ereal` -> `total`
  + canonicals `ereal_latticeType`, `ereal_distrLatticeType`, `ereal_orderType`, `ereal_blatticeType`,
    `ereal_tblatticeType`, lemmas `ereal_blatticeMixin`, `ereal_blatticeMixin` ->
    instances using `POrder_isTotal.Build`, `hasBottom.Build`, `hasTop.Build`
  + canonicals `adde_monoid`, `adde_comoid`, `mule_mulmonoid` -> instance using `isMulLaw.Build`
  + notations `maxe`, `mine`: `fun_scope` -> `function_scope`
  + canonicals `mule_monoid`, `mule_comoid` -> instance using `isComLaw.Build`
  + canonicals `maxe_monoid`, `maxe_comoid` -> instance using `isLaw.Build`

- in `reals.v`:
  + module `Real` (packed class) -> mixin `ArchimedeanField_isReal`
    with fields `sup_upper_bound_subdef`, `sup_adherent_subdef`,
	structure `Real`
  + canonicals `Rint_keyed`, `Rint_opprPred`, `Rint_addrPred`, `Rint_mulrPred`, `Rint_zmodPred`,
    `Rint_semiringPred`, `Rint_smulrPred`, `Rint_subringPred`
	-> instance using `GRing.isSubringClosed.Build`

- in `topology.v`:
  + canonicals `linear_eqType`, `linear_choiceType` ->
    instances using `gen_eqMixin`, `gen_choiceMixin`
  + canonical `gen_choiceMixin` -> instance using `isPointed.Build`
  + module `Filtered` (packed class) -> mixin `isFiltered` with field `nbhs`,
    structure `Filtered`
  + now use `set_system`:
    * definitions `filter_from`, `filter_prod`, `cvg_to`, `type_of_filter`, `lim_in`,
	  `Build_ProperFilter`, `filter_ex`, `fmap`, `fmapi`, `globally`, `in_filter_prod`,
	  `within`, `subset_filter`, `powerset_filter_from`, `principal_filter`, `locally_of`,
	  `sup_subbase`, `cluster`, `compact`, `near_covering`, `near_covering_within`,
	  `compact_near`, `nbhs_`, `weak_ent`, `sup_ent`, `cauchy`, `cvg_cauchy`, `cauchy_ex.Build`,
	  `cauchy_ball`
	* classes `Filter`, `ProperFilter'`, `UltraFilter`
	* instances `fmap_proper_filter`, `fmapi_filter`, `fmapi_proper_filter`,
	  `filter_prod_filter`, `filter_prod1`, `filter_prod2`
	* record `in_filter`
	* structure `filter_on`
	* variant `nbhs_subspace_spec`
	* lemmas `nearE`, `eq_near`, `nbhs_filterE`, `cvg_refl`, `cvg_trans`, `near2_curry`,
	  `near_swap`, `filterP_strong`, `filter_nbhsT`, `nearT`, `filter_not_empty_ex`,
	  `filter_ex_subproof`, `filter_getP`, `near`, `nearW`, `filterE`, `filter_app`,
	  `filter_app2`, `filter_app3`, `filterS2`, `filterS3`, `nearP_dep`, `filter2P`,
	  `filter_ex2`, `filter_fromP`, `filter_fromTP`, `filter_bigIP`, `filter_forall`,
	  `filter_imply`, `fmapEP`, `fmapiE`, `cvg_id`, `appfilterP`, `cvg_app`, `cvgi_app`,
	  `cvg_comp`, `cvgi_comp`, `near_eq_cvg`, `eq_cvg`, `neari_eq_loc`, `cvg_near_const`,
	  `near_pair`, `near_map`, `near_map2`, `near_mapi`, `filter_pair_set`,
	  `filter_pair_near_of`, `cvg_pair`, `cvg_comp2`, `near_powerset_map`,
	  `near_powerset_map_monoE`, `cvg_fmap`, `continuous_cvg`, `continuous_is_cvg`,
	  `continuous2_cvg`, `cvg_near_cst`, `is_cvg_near_cst`, `cvg_cst`, `is_cvg_cst`,
	  `fmap_within_eq`, `cvg_image`, `cvg_fmap2`, `cvg_within_filter`, `cvg_app_within`,
	  `meets_openr`, `meets_openl`, `meetsxx`, `proper_meetsxx`, `ultra_cvg_clusterE`,
	  `ultraFilterLemma`, `compact_ultra`, `proper_image`, `in_ultra_setVsetC`,
	  `ultra_image`, `filter_finI`, `close_cvg`, `discrete_cvg`, `nbhs_E`, `cvg_closeP`,
	  `cvg_mx_entourageP`, `cvg_fct_entourageP`, `fcvg_ball2P`, `cvg_ball2P`, `cauchy_cvgP`,
	  `mx_complete`, `Uniform_isComplete.Build`, `cauchy_ballP`, `cauchy_exP`, `cauchyP`,
      `compact_cauchy_cvg`, `pointwise_cvgE`, `pointwise_uniform_cvg`, `cvg_sigL`, `uniform_restrict_cvg`,
	  `cvg_uniformU`, `cvg_uniform_set0`, `fam_cvgP`, `family_cvg_subset`,
	  `family_cvg_finite_covers`, `fam_cvgE`, `Nbhs_isTopological`, `compact_open_fam_compactP`,
      `compact_cvg_within_compact`, `nbhs_subspace`, `subspace_cvgP`, `uniform_limit_continuous`,
	  `uniform_limit_continuous_subspace`, `pointwise_compact_cvg`
	* `t` in module type `PropInFilterSig`
  + canonical `matrix_filtered` -> instance using `isFiltered.Build`
  + now use `nbhs` instead of `[filter of ...]`
    * notations `-->`, `E @[ x --> F ]`, `f @ F`, ```E `@[ x --> F ]```, ```f `@ G```,
	  `{ptws, F --> f }`
  + notation `lim` is now a definition
  + canonical `filtered_prod` -> instances using `isFiltered.Build`, `selfFiltered.Build`
  + now use `set_system` and also `nbhsType` instead of `filteredType ...`
    * lemmas `cvg_ex`, `cvgP`, `cvg_toP`, `dvgP`, `cvgNpoint`, `eq_is_cvg`
  + canonicals `filter_on_eqType`, `filter_on_choiceType`, `filter_on_PointedType`,
    `filter_on_FilteredType` -> instances using `gen_eqMixin`, `gen_choiceMixin`,
	`isPointed.Build`, `isFiltered.Build`
  + canonical `bool_discrete_filter` -> instance using `hasNbhs.Build`
  + module `Topological` (packed class) -> mixin `Nbhs_isTopological`,
    structure `Topological`, type `topologicalType`
	* definition `open` now a field of the mixin
  + notation `continuous` now uses definition `continuous_at`
  + section `TopologyOfFilter` -> factory `Nbhs_isNbhsTopological`
  + section `TopologyOfOpen` -> factory `Pointed_isOpenTopological`
  + section `TopologyOfBase` -> factory `Pointed_isBaseTopological`
  + section `TopologyOfSubbase` -> factory `Pointed_isSubBaseTopological`
  + definition `Pointed_isSubBaseTopological`,
    canonicals `nat_filteredType`, `nat_topologicalType` ->
	instance using `Pointed_isBaseTopological.Build`
  + filter now explicit in the notation `X --> Y`
    * lemmas `cvg_addnr`, `cvg_subnr`, `cvg_mulnl`, `cvg_mulnr`, `cvg_divnr`
  + definition `prod_topologicalTypeMixin`, canonical `prod_topologicalType` ->
    instances using `hasNbhs.Build`, `Nbhs_isNbhsTopological.Build`
  + definition `matrix_topologicalTypeMixin`, canonical `matrix_topologicalType` ->
    instance using `Nbhs_isNbhsTopological.Build`
  + definitions `weak_topologicalTypeMixin`, `weak_topologicalType` ->
    instances using `Pointed.on`, `Pointed_isOpenTopological.Build`
  + definitions `sup_topologicalTypeMixin`, `sup_topologicalType` ->
    instances using `Pointed.on` and `Pointed_isSubBaseTopological.Build`
  + definition `product_topologicalType` -> definition `product_topology_def`
    and instance using `Topological.copy`
  + in `lim_id`: `nbhs` now explicit
  + canonical `bool_discrete_topology` -> instance using `bool_discrete_topology`
  + module `Uniform` (packed class) -> mixin `Nbhs_isUniform_mixin`,
    structure `Uniform`, type `uniformType`,
    factories `Nbhs_isUniform`, `isUniform`
  + definition `prod_uniformType_mixin`, canonical `prod_uniformType` ->
    instance using `Nbhs_isUniform.Build`
  + definition `matrix_uniformType_mixin`, canonical `matrix_uniformType` ->
    instance using `Nbhs_isUniform.Build`
  + definitions `weak_uniform_mixin`, `weak_uniformType` -> instance
    using `Nbhs_isUniform.Build`
  + definitions `fct_uniformType_mixin`, `fct_topologicalTypeMixin`,
    `generic_source_filter`, `fct_topologicalType`, `fct_uniformType` ->
	definition `arrow_uniform` and instance using `arrow_uniform`
  + definitions `sup_uniform_mixin`, `sup_uniformType` -> instance using
    `Nbhs_isUniform.Build`
  + definition `product_uniformType` -> instance using `Uniform.copy`
  + definition `discrete_uniformType` -> instance using `Choice.on`,
    `Choice.on`, `discrete_uniform_mixin`
  + module `PseudoMetric` (packed class) -> factory `Nbhs_isPseudoMetric`
  + definition `ball` now a field of factory `Nbhs_isPseudoMetric`
  + definition `matrix_pseudoMetricType_mixin`, canonical `matrix_pseudoMetricType` ->
    instance using `Uniform_isPseudoMetric.Build`
  + definition `prod_pseudoMetricType_mixin`, canonical `prod_pseudoMetricType` ->
    instance using `Uniform_isPseudoMetric.Build`
  + definition `fct_pseudoMetricType_mixin`, canonical `fct_pseudoMetricType` ->
    instance using `Uniform_isPseudoMetric.Build`
  + canonical `quotient_subtype` -> instance using `Quotient.copy`
  + canonical `quotient_eq` -> instance using `[Sub ... of ... by %/]`
  + canonical `quotient_choice` -> instance using `[Choice of ... by <:]`
  + canonical `quotient_pointed` -> instance using `isPointed.Build`
  + in definition `quotient_topologicalType_mixin`:
    `topologyOfOpenMixin` -> `Pointed_isOpenTopological.Build`
  + canonical `quotient_topologicalType` -> instance using `quotient_topologicalType_mixin`
  + lemma `repr_comp_continuous` uses the notation `\pi_` instead of `... == ... %[mod ...]`
  + definition `discrete_pseudoMetricType` -> instead using `discrete_pseudometric_mixin`
  + module `Complete` (packed class) -> mixin `Uniform_isComplete`,
    structure `Complete`, type `completeType`
	  * lemma `cauchy_cvg` now a mixin field
  + canonical `matrix_completeType` -> instance using `Uniform_isComplete.Build`
  + canonical `fun_completeType` -> instance using `Uniform_isComplete.Build`
  + module `CompletePseudoMetric` (packed class) -> structure `CompletePseudoMetric`
  + matrix instance using `Uniform_isComplete.Build`
  + function instance using `Uniform_isComplete.Build`
  + module `regular_topology` -> instances using ` Pointed.on`,
    `hasNbhs.Build`, `Nbhs_isPseudoMetric.Build`
  + in module `numFieldTopology`:
    * `realType`, `rcfType`, `archiFieldType`, `realFieldType`, `numClosedFieldType`,
	  `numFieldType` instances using `PseudoMetric.copy`
  + definition `fct_RestrictedUniform`, `fct_RestrictedUniformTopology`, canonical
    `fct_RestrictUniformFilteredType`, `fct_RestrictUniformTopologicalType`, `fct_restrictedUniformType`
    ->
    definition `uniform_fun`, instance using `Unifom.copy` for ```{uniform` _ -> _}```
  + definitions `fct_Pointwise`, `fct_PointwiseTopology`, canonicals `fct_PointwiseFilteredType`,
    `fct_PointwiseTopologicalType` -> definition `pointwise_fun`, instance using `Topological.copy`
  + definition `compact_openK_topological_mixin`, canonical `compact_openK_filter`,
    `compact_openK_topological` -> instances using `Pointed.on`,
    `hasNbhs.Build`, `compact_openK_openE_subproof` for `compact_openK`
  + canonical `compact_open_pointedType`, definition `compact_open_topologicalType`,
    canonicals `compact_open_filtered`, `compact_open_filtered` -> definition `compact_open_def`,
	instances using `Pointed.on`, `Nbhs.copy`, `Pointed.on`, `Nbhs_isTopological`
  + definitions `weak_pseudoMetricType_mixin`, `weak_pseudoMetricType` -> lemmas
    `weak_pseudo_metric_ball_center`, `weak_pseudo_metric_entourageE`, instance using `niform_isPseudoMetric.Build`
  + definition `countable_uniform_pseudoMetricType_mixin` -> module `countable_uniform`
    with definition `type`, instances using `Uniform.on`, `Uniform_isPseudoMetric.Build`,
	lemma `countable_uniform_bounded`, notation `countable_uniform`
  + definitions `sup_pseudoMetric_mixin`, `sup_pseudoMetricType`, `product_pseudoMetricType` ->
    instances using `PseudoMetric.on`, `PseudoMetric.copy`
  + definitions `subspace_pointedType`, `subspace_topologicalMixin`, canonicals `subspace_filteredType`,
    `subspace_topologicalType` -> instance using `Choice.copy`, `isPointed.Build`, `hasNbhs.Build`,
	lemmas `nbhs_subspaceP_subproof`, `nbhs_subspace_singleton`, `nbhs_subspace_nbhs`, instance using
	`Nbhs_isNbhsTopological.Build`
  + definition `subspace_uniformMixin`, canonical `subspace_uniformType` -> instance using
    `Nbhs_isUniform_mixin.Build`
  + definition `subspace_pseudoMetricType_mixin`, canonical `subspace_pseudoMetricType` -> lemmas `subspace_pm_ball_center`,
    `subspace_pm_ball_sym`, `subspace_pm_ball_triangle`, `subspace_pm_entourageE`, instance using
    `Uniform_isPseudoMetric.Build`
  + section `gauges` -> module `gauge`
    * `gauge_pseudoMetricType` -> `gauge.type` (instances using `Uniform.on`, `PseudoMetric.on`)
	* `gauge_uniformType` -> `gauge.type`

- in `cantor.v`:
	+ in definition `tree_of` and lemma `cantor_like_finite_prod`:
	  `pointed_discrete` -> `pointed_discrete_topology`

- in `normedtype.v`:
  + module `PseudoMetricNormedZmodule` (packed class) ->
    mixin `NormedZmod_PseudoMetric_eq` (with field `pseudo_metric_ball_norm`),
	structure `PseudoMetricNormedZmod`
  + now use `set_system`:
    * definitions `pinfty_nbhs`, `ninfty_nbhs`, `dominated_by`, `strictly_dominated_by`,
	  `bounded_near`, `sub_klipschitz`, `lipschitz_on`, `sub_lipschitz`
	* lemmas `cvgrnyP`, `cvgenyP`, `fcvgrPdist_lt`, `cvgrPdist_lt`, `cvgrPdistC_lt`,
	  `cvgr_dist_lt`, `cvgr_distC_lt`, `cvgr_dist_le`, `cvgr_distC_le`, `cvgr0Pnorm_lt`,
	  `cvgr0_norm_lt`, `cvgr0_norm_le`, `cvgrPdist_le`, `cvgrPdist_ltp`, `cvgrPdist_lep`,
	  `cvgrPdistC_le`, `cvgrPdistC_ltp`, `cvgrPdistC_lep`, `cvgr0Pnorm_le`, `cvgr0Pnorm_ltp`,
	  `cvgr0Pnorm_lep`, `cvgr_norm_lt`, `cvgr_norm_le`, `cvgr_norm_gt`, `cvgr_norm_ge`,
	  `cvgr_neq0`, `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_gt`, `real_cvgr_ge`, `cvgr_lt`,
	  `cvgr_le`, `cvgr_gt`, `cvgr_ge`, `sub_dominatedl`, `sub_dominatedr`, `ex_dom_bound`,
	  `ex_strict_dom_bound`, `sub_boundedr`, `sub_boundedl`, `ex_bound`, `ex_strict_bound`,
	  `ex_strict_bound_gt0`, `klipschitzW`, `cvg_bounded`, `fcvgr2dist_ltP`, `cvgr2dist_ltP`,
	  `cvgr2dist_lt`
  + module `NormedModule` (packed class) ->
    mixin `PseudoMetricNormedZmod_Lmodule_isNormedModule`,
	structure `NormedModule`
  + module and section `regular_topology` -> section `regular_topology`
    with instances using `Num.NormedZmodule.on`, `NormedZmod_PseudoMetric_eq.Build`,
	`seudoMetricNormedZmod_Lmodule_isNormedModule.Build`
  + in module `numFieldNormedType`
	* `realType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`
	* `rcfType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`
	* `archiFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`
	* `realFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`, `Num.RealField.on`
	* `numClosedFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`, `Num.ClosedField.on`
	* `numFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`, `Num.NumField.on`
  + in lemma `norm_lim_id`: now explicit use of `nbhs`
  + definition `matrix_PseudoMetricNormedZmodMixin` and canonical `matrix_normedModType`
    -> instance using `PseudoMetricNormedZmod_Lmodule_isNormedModule.Build`
  + definition `prod_pseudoMetricNormedZmodMixin` and canonical `prod_normedModType`
    -> instance using `PseudoMetricNormedZmod_Lmodule_isNormedModule.Build`
  + module `CompleteNormedModule` (packed class) -> structure `CompleteNormedModule`
  + canonicals `R_regular_completeType`, `R_regular_CompleteNormedModule` ->
    instance using `Uniform_isComplete.Build`
  + canonicals `R_completeType` and `R_CompleteNormedModule` -> instance using `Complete.on`
  + now use `cvgn` instead of `cvg`:
    * lemma `cvg_seq_bounded`

- in `Rstruct.v`:
  + canonicals `R_eqMixin`, `R_eqType` -> instance using `hasDecEq.Build`
  + definition `R_choiceMixin` and canonical `R_choiceType` -> instance using `hasChoice.Build`
  + definition `R_zmodMixin` and canonical `R_zmodType` -> instance using `isZmodule.Build`
  + definition `R_ringMixin` and canonicals `R_ringType`, `R_comRingType` ->
    instances using `Zmodule_isRing.Build`, `Ring_hasCommutativeMul.Build`
  + canonicals `Radd_monoid`, `Radd_comoid` -> instance using `isComLaw.Build`
  + canonicals `Rmul_monoid`, `Rmul_comoid` -> instance using `isComLaw.Build`
  + canonical `Rmul_mul_law` -> instance using `isMulLaw.Build`
  + canonical `Radd_add_law` -> instance using `isAddLaw.Build`
  + definition `R_unitRingMixin` and canonical `R_unitRing` -> instance using `Ring_hasMulInverse.Build`
  + canonicals `R_comUnitRingType` and `R_idomainType` ->
    instance using `ComUnitRing_isIntegral.Build`
  + in lemma `R_fieldMixin`: `GRing.Field.mixin_of` -> `GRing.field_axiom`
  + definition `Definition` and canonical `R_fieldType` -> instance using `UnitRing_isField.Build`
  + definition `R_numMixin`, canonicals `R_porderType`, `R_numDomainType`, `R_normedZmodType`, `R_numFieldType`
    -> instance using `IntegralDomain_isNumRing.Build`
  + in lemma `R_total`: `totalPOrderMixin` -> `total`
  + canonicals `R_latticeType`, `R_distrLatticeType`, `R_orderType`, `R_realDomainType`, `R_realFieldType`
    -> instance using `POrder_isTotal.Build`
  + in lemmas `Rarchimedean_axiom`, `Rreal_closed_axiom`: `R_numDomainType` -> `[the numDomainType of R : Type]`
  + canonical `R_realArchiFieldType` -> instance using `RealField_isArchimedean.Build`
  + canonical `R_rcfType` -> instance using `RealField_isClosed.Build`
  + definition `real_realMixin` and canonical `real_realType` -> instance using `ArchimedeanField_isReal.Build`
- in `prodnormedzmodule.v`:
  + definition `normedZmodMixin` and canonical `normedZmodType` ->
    instance using `Num.Zmodule_isNormed.Build`

- in `ereal.v`:
  + canonical `ereal_pointed` -> instance using `isPointed.Build`
  + definitions `ereal_dnbhs`, `ereal_nbhs` -> now use `set_system`
  + canonical `ereal_ereal_filter` -> instance using `hasNbhs.Build`
  + definition `ereal_topologicalMixin`, canonical `ereal_topologicalType`,
    definitions `ereal_pseudoMetricType_mixin`, `ereal_uniformType_mixin`,
	canonicals `ereal_uniformType`, `ereal_pseudoMetricType` ->
	instance using `Nbhs_isPseudoMetric.Build`

- "moved" from `normedtype.v` to `Rstruct.v`:
  + canonicals `R_pointedType`, `R_filteredType`, `R_topologicalType`, `R_uniformType`,
    `R_pseudoMetricType` -> instance using `PseudoMetric.copy`

- in `realfun.v`:
  + now explicitly display the filter in the notation `X --> Y`:
    * lemma s`cvg_at_rightP`, `cvg_at_leftP`, `cvge_at_rightP`, `cvge_at_leftP`

- in `sequences.v`:
  + the lemmas and the notations (in particular, bigop notations) that were using
    `cvg` or `cvg (... @ \oo)`/`lim` are now using `cvgn`/`limn`
    and now explicitly mention the filter in the notation `X --> Y`

- in `trigo.v`:
  + now make explicit mention of the filter:
    * definitions `sin`, `cos`
    * lemmas `cvg_series_cvg_series_group`, `lt_sum_lim_series`, `is_cvg_series_sin_coeff`,
	  `sinE`, `cvg_sin_coeff'`, `is_cvg_series_cos_coeff`, `cosE`, `cvg_cos_coeff'`

- in `itv.v`:
  + canonical `itv_subType` -> instance using `[isSub for ... ]`
  + definitions `itv_eqMixin`, `itv_choiceMixin` and canonicals `itv_eqType`, `itv_choiceType`
    -> instance using `[Choice of ... by <:]`
  + definition `itv_porderMixin` and canonical `itv_porderType` -> instance using
    `[SubChoice_isSubPOrder of ... by <: with ...]`

- in `landau.v`:
  + now use `set_system`
    * structures `littleo_type`, `bigO_type`, `bigOmega_type`, `bigTheta_type`
	* lemmas `littleo_class`, `littleoE`, `littleo`, `bigO_exP`, `bigO_class`,
	  `bigO_clone`, `bigOP`, `bigOE`, `bigOmegaP`, `bigThetaP`
	* definitions `littleo_clone`, `the_littleo`, `littleoP`, `the_bigO`,
	  `bigOmega_clone`, `the_bigOmega`, `is_bigOmega`, `bigTheta_clone`,
	  `is_bigTheta`
	* variants `littleo_spec`, `bigOmega_spec`, `bigTheta_spec`
	* notation `PhantomF`
	* facts `is_bigOmega_key`, `is_bigTheta_key`
	* canonicals `the_littleo_littleo`, `the_bigO_bigO`, `the_littleo_bigO`,
	  `is_bigOmega_keyed`, `the_bigOmega_bigOmega`, `is_bigTheta_keyed`,
	  `the_bigTheta_bigTheta`
  + canonical `littleo_subtype` -> instance using `[isSub for ...]`
  + canonical `bigO_subtype` -> instance using `[isSub for ...]`
  + in `linear_for_continuous`:
    * `GRing.Scale.op s_law` -> `GRing.Scale.Law.sort`
	* argument `s_law` removed
  + canonical `bigOmega_subtype` -> instance using `[isSub for ...]`
  + canonical `bigTheta_subtype` -> instance using `[isSub for ...]`

- in `forms.v`:
  + module `Bilinear` (packed class) -> mixin `isBilinear`, structure `Bilinear`,
    definition `bilinear_for`, factory `bilinear_isBilinear`, new module `Bilinear`
	containing the definition `map`
  + canonical `mulmx_bilinear` -> lemma `mulmx_is_bilinear` and instance using
    `bilinear_isBilinear.Build`

- in `derive.v`
  + in notation `'d`, `differentiable`, `is_diff`: `[filter of ...]` -> `nbhs F`
  + canonical `mulr_linear` -> instance using `isLinear.Build`
  + canonical `mulr_rev_linear` -> instance using `isLinear.Build`
  + canonical `mulr_bilinear` -> lemma `mulr_is_bilinear` and instance using `bilinear_isBilinear.Build`
  + `set (set ...)` -> `set_system ...`
- in `esum.v`:
  + several occurrences of `cvg`/`lim` changed to `cvgn`/`limn` and
    usages of the notation `X --> Y` changed to `X @ F --> Y` (with an explicit filter)
    * `is_cvg_pseries_inside_norm`
	* `is_cvg_pseries_inside`
	* `pseries_diffs_equiv`
    * `is_cvg_pseries_diffs_equiv`
	* `pseries_snd_diffs`
	* `expRE`
    * `dvg_riemannR`

- in `numfun.v`:
  + canonicals `fimfun_mul`, `fimfun_ring`, `fimfun_ringType`, definition `fimfun_ringMixin`
    -> instances using `GRing.isMulClosed.Build` and `[SubZmodule_isSubRing of ... by <:]`
  + definition `fimfun_comRingMixin`, canonical `fimfun_comRingType` ->
    instance using `[SubRing_isSubComRing of ... by <:]`

- in `measure.v`
  + canonicals `salgebraType_eqType`, `salgebraType_choiceType`, `salgebraType_ptType`
    -> instance using `Pointed.on`
  + filter now explicit in:
    * definitions `sigma_additive`, `semi_sigma_additive`
	* lemmas `nondecreasing_cvg_mu`, `nonincreasing_cvg_mu`
  + canonicals `ring_eqType`, `ring_choiceType`, `ring_ptType` -> instance using `Pointed.on`

- in `lebesgue_measure.v`:
  + filter now explicit in lemmas `emeasurable_fun_cvg`,
    `ae_pointwise_almost_uniform`

- in `lebesgue_integral.v`:
  + canonical `mfun_subType` -> instance using `isSub.Build`
  + definitions `mfuneqMixin`, `mfunchoiceMixin`, canonicals `mfuneqType`,
    `mfunchoiceType` -> instance using `[Choice of ... by <:]`
  + canonicals `mfun_add`, `mfun_zmod`, `mfun_mul`, `mfun_subring`,
    `mfun_zmodType`, `mfun_ringType`, `mfun_comRingType`,
    definitions `mfun_zmodMixin`, `mfun_ringMixin`, `mfun_comRingMixin`,
	-> instances using `GRing.isSubringClosed.Build` and `[SubChoice_isSubComRing of ... <:]`
  + canonical `sfun_subType` -> instance using `isSub.Build`
  + definitions `sfuneqMixin`, `sfunchoiceMixin`,
    canonicals `sfuneqType`, `sfunchoiceType` ->
	instance using `[Choice of .. by <:]`
  + canonicals `sfun_add`, `sfun_zmod`, `sfun_mul`, `sfun_subring`, `sfun_zmodType`,
    `sfun_ringType`, `sfun_comRingType`,
    definitions `sfun_zmodMixin`, `sfun_ringMixin`, `sfun_comRingMixin`
	-> instances using `GRing.isSubringClosed.Build` and `[SubChoice_isSubComRing of ... by <:]`
  + now use `cvgn`/`limn` instead of `cvg`/`lim`:
    * lemmas `is_cvg_sintegral`, `nd_sintegral_lim_lemma`, `nd_sintegral_lim`, `nd_ge0_integral_lim`,
	  `dvg_approx`, `ecvg_approx`
  + filter now explicit in:
    * lemmas `approximation`, `approximation_sfun`, `cvg_monotone_convergence`

- in `kernel.v`:
  + notation `X --> Y` changed to `X @ F --< Y`
	* `measurable_fun_xsection_integral`
  + definition `prob_pointed` and canonical `probability_ptType` ->
    instance using `isPointed.Build`
  + canonicals `probability_eqType`, `probability_choiceType` ->
    instance using `gen_eqMixin` and `gen_choiceMixin`

- in `summability.v`:
  + `totally` now uses `set_system`

- in `altreals/discrete.v`:
  + canonical `pred_sub_subTypeP` -> instance using `[isSub for ...]`
  + definition `pred_sub_eqMixin` and canonical `pred_sub_eqType` ->
    instance using `[Equality of ... by <:]`
  + definition `pred_sub_choiceMixin` and canonical `pred_sub_choiceType` ->
    instance using `[Choice of ... <:]`
  + definition `pred_sub_countMixin` and `pred_sub_countType` ->
    instance using `[Countable of ... by <:]`
  + definitions `countable_countMixin` and `countable_countType` -> `countable_countMixin`
  + definitions `countable_choiceMixin` and `countable_choiceType` -> `countable_choiceMixin`

- in `altreals/xfinmap.v`:
  + in lemmas `enum_fset0` and `enum_fset1`: notation `[fintype of ...]` -> type constraint `... : finType`

- in `misc/uniform_bigO.v`:
  + in definition `OuO`: `[filter of ...]` -> `nbhs ...`

### Generalized

- in `cantor.v`:
  + in definition `cantor_space`: `product_uniformType` -> `prod_topology`
	* instances using `Pointed.on`, `Nbhs.on`, `Topological.on`

- in `topology.v`:
  + now use `nbhsType` instead of `topologicalType`
    * lemma `near_fun`
    * definition `discrete_space`
    * definition `discrete_uniform_mixin`
	* definition `discrete_ball`, lemma `discrete_ball_center`,
	  definition `discrete_pseudometric_mixin`

### Removed

- in `mathcomp_extra.v`:
  + coercion `choice.Choice.mixin`
  + lemmas `bigminr_maxr`, definitions `AC_subdef`, `oAC`, `opACE`, canonicals `opAC_law`, `opAC_com_law`
  + lemmas `some_big_AC`, `big_ACE`, `big_undup_AC`, `perm_big_AC`, `big_const_idem`,
    `big_id_idem`, `big_mkcond_idem`, `big_split_idem`, `big_id_idem_AC`, `bigID_idem`,
	`big_rem_AC`, `bigD1_AC`, `sub_big`, `sub_big_seq`, `sub_big_seq_cond`, `uniq_sub_big`,
	`uniq_sub_big_cond`, `sub_big_idem`, `sub_big_idem_cond`, `sub_in_big`, `le_big_ord`,
	`subset_big`, `subset_big_cond`, `le_big_nat`, `le_big_ord_cond`
  + lemmas `bigmax_le`, `bigmax_lt`, `lt_bigmin`, `le_bigmin`
  + lemmas `bigmax_mkcond`, `bigmax_split`, `bigmax_idl`, `bigmax_idr`, `bigmaxID`
  + lemmas `sub_bigmax`, `sub_bigmax_seq`, `sub_bigmax_cond`, `sub_in_bigmax`,
    `le_bigmax_nat`, `le_bigmax_nat_cond`, `le_bigmax_ord`, `le_bigmax_ord_cond`,
	`subset_bigmax`, `subset_bigmax_cond`
  + lemmas `bigmaxD1`, `le_bigmax_cond`, `le_bigmax`, `bigmax_sup`, `bigmax_leP`,
    `bigmax_ltP`, `bigmax_eq_arg`, `eq_bigmax`, `le_bigmax2`
  + lemmas `bigmin_mkcond`, `bigmin_split`, `bigmin_idl`, `bigmin_idr`, `bigminID`
  + lemmas `sub_bigmin`, `sub_bigmin_cond`, `sub_bigmin_seq`, `sub_in_bigmin`,
    `le_bigmin_nat`, `le_bigmin_nat_cond`, `le_bigmin_ord`, `le_bigmin_ord_cond`,
	`subset_bigmin`, `subset_bigmin_cond`
  + lemmas `bigminD1`, `bigmin_le_cond`, `bigmin_le`, `bigmin_inf`, `bigmin_geP`,
    `bigmin_gtP`, `bigmin_eq_arg`, `eq_bigmin`

- in `boolp.v`:
  + definitions `dep_arrow_eqType`, `dep_arrow_choiceClass`, `dep_arrow_choiceType`

- in `classical_sets.v`:
  + notations `PointedType`, `[pointedType of ...]`

- in `cardinality.v`:
  + lemma `countable_setT_countMixin`

- in `constructive_ereal.v`:
  + canonicals `isLaw.Build`, `mine_comoid`

- in `topology.v`:
  + structure `source`, definition `source_filter`
  + definition `filter_of`, notation `[filter of ...]` (now replaced by `nbhs`), lemma `filter_of_filterE`
  + definition `open_of_nbhs`
  + definition `open_from`, lemma `open_fromT`
  + canonical `eventually_filter_source`
  + canonical `discrete_topological_mixin`
  + canonical `set_filter_source`
  + definitions `filtered_of_normedZmod`, `pseudoMetric_of_normedDomain`
  + definitions `fct_UniformFamily` (use `uniform_fun_family` instead), canonicals `fct_UniformFamilyFilteredType`,
   `fct_UniformFamilyTopologicalType`, `fct_UniformFamilyUniformType`

- in `cantor.v`:
  + definition `pointed_discrete`

- in `normedtype.v`:
  + `filtered_of_normedZmod`
  + section `pseudoMetric_of_normedDomain`
    * lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`, `nbhs_ball_normE`
	* definition `pseudoMetric_of_normedDomain`
  + lemma `normrZ`
  + canonical `matrix_normedZmodType`
  + lemmas `eq_cvg`, `eq_is_cvg`

- in `convex.v`:
  + field `convexspacechoiceclass`, canonicals `conv_eqType`, `conv_choiceType`, `conv_choiceType`

- in `measure.v`:
  + field `ptclass` in mixin `isSemiRingOfSets`
  + canonicals `ringOfSets_eqType`, `ringOfSets_choiceType`,
    `ringOfSets_ptType`, `algebraOfSets_eqType`, `algebraOfSets_choiceType`,
	`algebraOfSets_ptType`, `measurable_eqType`, `measurable_choiceType`,
	`measurable_ptType`
  + field `ptclass` in factory `isAlgebraOfSets`
  + field `ptclass` in factory `isMeasurable`

- in `lebesgue_measure.v`:
  + no more "pointed class" argument in definition `ereal_isMeasurable`

- in `lebesgue_stieltjes_measure.v`
  + lemma `sigmaT_finite_lebesgue_stieltjes_measure` turned into a `Let`

- in `altreals/discrete.v`:
  + notation `[countable of ...]`

## [0.7.0] - 2024-01-19

### Added

- in `mathcomp_extra.v`:
  + lemmas `last_filterP`,
    `path_lt_filter0`, `path_lt_filterT`, `path_lt_head`, `path_lt_last_filter`,
	`path_lt_le_last`

- new file `contra.v`
  + lemma `assume_not`
  + tactic `assume_not`
  + lemma `absurd_not`
  + tactics `absurd_not`, `contrapose`
  + tactic notations `contra`, `contra : constr(H)`, `contra : ident(H)`,
    `contra : { hyp_list(Hs) } constr(H)`, `contra : { hyp_list(Hs) } ident(H)`,
	 `contra : { - } constr(H)`
  + lemma `absurd`
  + tactic notations `absurd`, `absurd constr(P)`, `absurd : constr(H)`,
    `absurd : ident(H)`, `absurd : { hyp_list(Hs) } constr(H)`,
	 `absurd : { hyp_list(Hs) } ident(H)`

- in `topology.v`:
  + lemma `filter_bigI_within`
  + lemma `near_powerset_map`
  + lemma `near_powerset_map_monoE`
  + lemma `fst_open`
  + lemma `snd_open`
  + definition `near_covering_within`
  + lemma `near_covering_withinP`
  + lemma `compact_setM`
  + lemma `compact_regular`
  + lemma `fam_compact_nbhs`
  + definition `compact_open`, notation `{compact-open, U -> V}`
  + notation `{compact-open, F --> f}`
  + definition `compact_openK`
  + definition `compact_openK_nbhs`
  + instance `compact_openK_nbhs_filter`
  + definition `compact_openK_topological_mixin`
  + canonicals `compact_openK_filter`, `compact_openK_topological`,
	`compact_open_pointedType`
  + definition `compact_open_topologicalType`
  + canonicals `compact_open_filtered`, `compact_open_topological`
  + lemma `compact_open_cvgP`
  + lemma `compact_open_open`
  + lemma `compact_closedI`
  + lemma `compact_open_fam_compactP`
  + lemma `compact_equicontinuous`
  + lemma `uniform_regular`
  + lemma `continuous_curry`
  + lemma `continuous_uncurry_regular`
  + lemma `continuous_uncurry`
  + lemma `curry_continuous`
  + lemma `uncurry_continuous`

- in `ereal.v`:
  + lemma `ereal_supy`

- in file `normedtype.v`,
  + new lemma `continuous_within_itvP`.

- in file `realfun.v`,
  + definitions `itv_partition`, `itv_partitionL`, `itv_partitionR`,
    `variation`, `variations`, `bounded_variation`, `total_variation`,
    `neg_tv`, and `pos_tv`.

  + new lemmas `left_right_continuousP`,
    `nondecreasing_funN`, `nonincreasing_funN`

  + new lemmas `itv_partition_nil`, `itv_partition_cons`, `itv_partition1`,
    `itv_partition_size_neq0`, `itv_partitionxx`, `itv_partition_le`,
    `itv_partition_cat`, `itv_partition_nth_size`,
    `itv_partition_nth_ge`, `itv_partition_nth_le`,
    `nondecreasing_fun_itv_partition`, `nonincreasing_fun_itv_partition`,
    `itv_partitionLP`, `itv_partitionRP`, `in_itv_partition`,
    `notin_itv_partition`, `itv_partition_rev`,

  + new lemmas `variation_zip`, `variation_prev`, `variation_next`, `variation_nil`,
    `variation_ge0`, `variationN`, `variation_le`, `nondecreasing_variation`,
    `nonincreasing_variation`, `variationD`, `variation_itv_partitionLR`,
    `le_variation`, `variation_opp_rev`, `variation_rev_opp`

  + new lemmas `variations_variation`, `variations_neq0`, `variationsN`, `variationsxx`

  + new lemmas `bounded_variationxx`, `bounded_variationD`, `bounded_variationN`,
    `bounded_variationl`, `bounded_variationr`, `variations_opp`,
    `nondecreasing_bounded_variation`

  + new lemmas `total_variationxx`, `total_variation_ge`, `total_variation_ge0`,
    `bounded_variationP`, `nondecreasing_total_variation`, `total_variationN`,
	  `total_variation_le`, `total_variationD`, `neg_tv_nondecreasing`,
    `total_variation_pos_neg_tvE`, `fine_neg_tv_nondecreasing`,
    `neg_tv_bounded_variation`, `total_variation_right_continuous`,
    `neg_tv_right_continuous`, `total_variation_opp`,
    `total_variation_left_continuous`, `total_variation_continuous`

- in `lebesgue_stieltjes_measure.v`:
  + `sigma_finite_measure` HB instance on `lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + `sigma_finite_measure` HB instance on `lebesgue_measure`

- in `lebesgue_integral.v`:
  + `sigma_finite_measure` instance on product measure `\x`

### Changed

- in `topology.v`:
  + lemmas `nbhsx_ballx` and `near_ball` take a parameter of type `R` instead of `{posnum R}`
  + lemma `pointwise_compact_cvg`

### Generalized

- in `realfun.v`:
  + lemmas `nonincreasing_at_right_cvgr`, `nonincreasing_at_left_cvgr`
  + lemmas `nondecreasing_at_right_cvge`, `nondecreasing_at_right_is_cvge`,
    `nonincreasing_at_right_cvge`, `nonincreasing_at_right_is_cvge`

- in `realfun.v`:
  + lemmas `nonincreasing_at_right_is_cvgr`, `nondecreasing_at_right_is_cvgr`

## [0.6.7] - 2024-01-09

### Added

- in `boolp.v`:
  + tactic `eqProp`
  + variant `BoolProp`
  + lemmas `PropB`, `notB`, `andB`, `orB`, `implyB`, `decide_or`, `not_andE`,
    `not_orE`, `orCA`, `orAC`, `orACA`, `orNp`, `orpN`, `or3E`, `or4E`, `andCA`,
	 `andAC`, `andACA`, `and3E`, `and4E`, `and5E`, `implyNp`, `implypN`,
	 `implyNN`, `or_andr`, `or_andl`, `and_orr`, `and_orl`, `exists2E`,
	 `inhabitedE`, `inhabited_witness`

- in `topology.v`,
  + new lemmas `perfect_set2`, and `ent_closure`.
  + lemma `clopen_surj`
  + lemma `nbhs_dnbhs_neq`
  + lemma `dnbhs_ball`

- in `constructive_ereal.v`
  + lemma `lee_subgt0Pr`

- in `ereal.v`:
  + lemmas `ereal_sup_le`, `ereal_inf_le`

- in `normedtype.v`:
  + hints for `at_right_proper_filter` and `at_left_proper_filter`
  + definition `lower_semicontinuous`
  + lemma `lower_semicontinuousP`
  + lemma `not_near_at_rightP`
  + lemmas `withinN`, `at_rightN`, `at_leftN`, `cvg_at_leftNP`, `cvg_at_rightNP`
  + lemma `dnbhsN`
  + lemma `limf_esup_dnbhsN`
  + definitions `limf_esup`, `limf_einf`
  + lemmas `limf_esupE`, `limf_einfE`, `limf_esupN`, `limf_einfN`

- in `sequences.v`:
  + lemma `minr_cvg_0_cvg_0`
  + lemma `mine_cvg_0_cvg_fin_num`
  + lemma `mine_cvg_minr_cvg`
  + lemma `mine_cvg_0_cvg_0`
  + lemma `maxr_cvg_0_cvg_0`
  + lemma `maxe_cvg_0_cvg_fin_num`
  + lemma `maxe_cvg_maxr_cvg`
  + lemma `maxe_cvg_0_cvg_0`
  + lemmas `limn_esup_lim`, `limn_einf_lim`

- in file `cantor.v`,
  + definitions `cantor_space`, `cantor_like`, `pointed_discrete`, and
    `tree_of`.
  + new lemmas `cantor_space_compact`, `cantor_space_hausdorff`,
    `cantor_zero_dimensional`, `cantor_perfect`, `cantor_like_cantor_space`,
    `tree_map_props`, `homeomorphism_cantor_like`, and
    `cantor_like_finite_prod`.
  + new theorem `cantor_surj`.

- in `numfun.v`:
  + lemma `patch_indic`

- in `realfun.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`,
    `increasing_fun`, `decreasing_fun`
  + lemmas `cvg_addrl`, `cvg_addrr`, `cvg_centerr`, `cvg_shiftr`,
    `nondecreasing_cvgr`,
	`nonincreasing_at_right_cvgr`,
	`nondecreasing_at_right_cvgr`,
	`nondecreasing_cvge`, `nondecreasing_is_cvge`,
	`nondecreasing_at_right_cvge`, `nondecreasing_at_right_is_cvge`,
	`nonincreasing_at_right_cvge`, `nonincreasing_at_right_is_cvge`
  + lemma `cvg_at_right_left_dnbhs`
  + lemma `cvg_at_rightP`
  + lemma `cvg_at_leftP`
  + lemma `cvge_at_rightP`
  + lemma `cvge_at_leftP`
  + lemma `lime_sup`
  + lemma `lime_inf`
  + lemma `lime_supE`
  + lemma `lime_infE`
  + lemma `lime_infN`
  + lemma `lime_supN`
  + lemma `lime_sup_ge0`
  + lemma `lime_inf_ge0`
  + lemma `lime_supD`
  + lemma `lime_sup_le`
  + lemma `lime_inf_sup`
  + lemma `lim_lime_inf`
  + lemma `lim_lime_sup`
  + lemma `lime_sup_inf_at_right`
  + lemma `lime_sup_inf_at_left`
  + lemmas `lime_sup_lim`, `lime_inf_lim`

- in file `measure.v`
  + add lemmas `ae_eq_subset`, `measure_dominates_ae_eq`.

- in `lebesgue_measure.v`
  + lemma `lower_semicontinuous_measurable`

- in `lebesgue_integral.v`:
  + definition `locally_integrable`
  + lemmas `integrable_locally`, `locally_integrableN`, `locally_integrableD`,
    `locally_integrableB`
  + definition `iavg`
  + lemmas `iavg0`, `iavg_ge0`, `iavg_restrict`, `iavgD`
  + definitions `HL_maximal`
  + lemmas `HL_maximal_ge0`, `HL_maximalT_ge0`,
    `lower_semicontinuous_HL_maximal`, `measurable_HL_maximal`,
    `maximal_inequality`

- in `charge.v`
  + definition `charge_of_finite_measure` (instance of `charge`)
  + lemmas `dominates_cscalel`, `dominates_cscaler`
  + definition `cpushforward` (instance of `charge`)
  + lemma `dominates_pushforward`
  + lemma `cjordan_posE`
  + lemma `jordan_posE`
  + lemma `cjordan_negE`
  + lemma `jordan_negE`
  + lemma `Radon_Nikodym_sigma_finite`
  + lemma `Radon_Nikodym_fin_num`
  + lemma `Radon_Nikodym_integral`
  + lemma `ae_eq_Radon_Nikodym_SigmaFinite`
  + lemma `Radon_Nikodym_change_of_variables`
  + lemma `Radon_Nikodym_cscale`
  + lemma `Radon_Nikodym_cadd`
  + lemma `Radon_Nikodym_chain_rule`

### Changed

- in `boolp.v`
  - lemmas `orC` and `andC` now use `commutative`

- moved from `topology.v` to `mathcomp_extra.v`
  + definition `monotonous`

- in `normedtype.v`:
  + lemmas `vitali_lemma_finite` and `vitali_lemma_finite_cover` now returns
    duplicate-free lists of indices

- in `sequences.v`:
  + change the implicit arguments of `trivIset_seqDU`
  + `limn_esup` now defined from `lime_sup`
  + `limn_einf` now defined from `limn_esup`

- moved from `lebesgue_integral.v` to `measure.v`:
  + definition `ae_eq`
  + lemmas
	`ae_eq0`,
	`ae_eq_comp`,
	`ae_eq_funeposneg`,
	`ae_eq_refl`,
	`ae_eq_trans`,
	`ae_eq_sub`,
	`ae_eq_mul2r`,
	`ae_eq_mul2l`,
	`ae_eq_mul1l`,
	`ae_eq_abse`

- in `charge.v`
  + definition `jordan_decomp` now uses `cadd` and `cscale`
  + definition `Radon_Nikodym_SigmaFinite` now in a module `Radon_Nikodym_SigmaFinite` with
    * definition `f`
    * lemmas `f_ge0`, `f_fin_num`, `f_integrable`, `f_integral`
    * lemma `change_of_variables`
    * lemma `integralM`
    * lemma `chain_rule`

### Renamed

- in `exp.v`:
  + `lnX` -> `lnXn`

- in `charge.v`:
  + `dominates_caddl` -> `dominates_cadd`

### Generalized

- in `lebesgue_measure.v`
  + an hypothesis of lemma `integral_ae_eq` is weakened

- in `lebesgue_integral.v`
  + `ge0_integral_bigsetU` generalized from `nat` to `eqType`

### Removed

- in `boolp.v`:
  + lemma `pdegen`

- in `forms.v`:
  + lemmas `eq_map_mx`, `map_mx_id`

## [0.6.6] - 2023-11-14

### Added

- in `mathcomp_extra.v`
  + lemmas `ge0_ler_normr`, `gt0_ler_normr`, `le0_ger_normr` and `lt0_ger_normr`
  + lemma `leq_ltn_expn`
  + lemma `onemV`

- in `classical_sets.v`:
  + lemma `set_cons1`
  + lemma `trivIset_bigcup`
  + definition `maximal_disjoint_subcollection`
  + lemma `ex_maximal_disjoint_subcollection`
  + lemmas `mem_not_I`, `trivIsetT_bigcup`

- in `constructive_ereal.v`:
  + lemmas `gt0_fin_numE`, `lt0_fin_numE`
  + lemmas `le_er_map`, `er_map_idfun`

- in `reals.v`:
  + lemma `le_inf`
  + lemmas `ceilN`, `floorN`

- in `topology.v`:
  + lemmas `closure_eq0`, `separated_open_countable`

- in `normedtype.v`:
  + lemmas `ball0`, `ball_itv`, `closed_ball0`, `closed_ball_itv`
  + definitions `cpoint`, `radius`, `is_ball`
  + definition `scale_ball`, notation notation ``` *` ```
  + lemmas `sub_scale_ball`, `scale_ball1`, `sub1_scale_ball`
  + lemmas `ball_inj`, `radius0`, `cpoint_ball`, `radius_ball_num`,
    `radius_ball`, `is_ballP`, `is_ball_ball`, `scale_ball_set0`,
    `ballE`, `is_ball_closure`, `scale_ballE`, `cpoint_scale_ball`,
	`radius_scale_ball`
  + lemmas `vitali_lemma_finite`, `vitali_lemma_finite_cover`
  + definition `vitali_collection_partition`
  + lemmas `vitali_collection_partition_ub_gt0`,
    `ex_vitali_collection_partition`, `cover_vitali_collection_partition`,
	`disjoint_vitali_collection_partition`
  + lemma `separate_closed_ball_countable`
  + lemmas `vitali_lemma_infinite`, `vitali_lemma_infinite_cover`
  + lemma `open_subball`
  + lemma `closed_disjoint_closed_ball`
  + lemma `is_scale_ball`
  + lemmas `scale_ball0`, `closure_ball`, `bigcup_ballT`

- in `sequences.v`:
  + lemma `nneseries_tail_cvg`

- in `exp.v`:
  + definition `expeR`
  + lemmas `expeR0`, `expeR_ge0`, `expeR_gt0`
  + lemmas `expeR_eq0`, `expeRD`, `expeR_ge1Dx`
  + lemmas `ltr_expeR`, `ler_expeR`, `expeR_inj`, `expeR_total`
  + lemmas `mulr_powRB1`, `fin_num_poweR`, `poweRN`, `poweR_lty`, `lty_poweRy`, `gt0_ler_poweR`
  + lemma `expRM`

- in `measure.v`:
  + lemmas `negligibleI`, `negligible_bigsetU`, `negligible_bigcup`
  + lemma `probability_setC`
  + lemma `measure_sigma_sub_additive_tail`
  + lemma `outer_measure_sigma_subadditive_tail`

- new `lebesgue_stieltjes_measure.v`:
  + notation `right_continuous`
  + lemmas `right_continuousW`, `nondecreasing_right_continuousP`
  + mixin `isCumulative`, structure `Cumulative`, notation `cumulative`
  + `idfun` instance of `Cumulative`
  + `wlength`, `wlength0`, `wlength_singleton`, `wlength_setT`, `wlength_itv`,
    `wlength_finite_fin_num`, `finite_wlength_itv`, `wlength_itv_bnd`, `wlength_infty_bnd`,
    `wlength_bnd_infty`, `infinite_wlength_itv`, `wlength_itv_ge0`, `wlength_Rhull`,
    `le_wlength_itv`, `le_wlength`, `wlength_semi_additive`, `wlength_ge0`,
    `lebesgue_stieltjes_measure_unique`
  + content instance of `hlength`
  + `cumulative_content_sub_fsum`,
    `wlength_sigma_sub_additive`, `wlength_sigma_finite`
  + measure instance of `hlength`
  + definition `lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + lemma `lebesgue_measurable_ball`
  + lemmas `measurable_closed_ball`, `lebesgue_measurable_closed_ball`
  + definition `vitali_cover`
  + lemma `vitali_theorem`

- in `lebesgue_integral.v`:
  + `mfun` instances for `expR` and `comp`
  + lemma `abse_integralP`

- in `charge.v`:
  + factory `isCharge`
  + Notations `.-negative_set`, `.-positive_set`
  + lemmas `dominates_cscale`, `Radon_Nikodym_cscale`
  + definition `cadd`, lemmas `dominates_caddl`, `Radon_Nikodym_cadd`

- in `probability.v`:
  + definition `mmt_gen_fun`, `chernoff`

- in `hoelder.v`:
  + lemmas `powR_Lnorm`, `minkowski`

### Changed

- in `normedtype.v`:
  + order of arguments of `squeeze_cvgr`

- moved from `derive.v` to `normedtype.v`:
  + lemmas `cvg_at_rightE`, `cvg_at_leftE`

- in `measure.v`:
  + order of parameters changed in `semi_sigma_additive_is_additive`,
    `isMeasure`

- in `lebesgue_measure.v`:
  + are now prefixed with `LebesgueMeasure`:
    * `hlength`, `hlength0`, `hlength_singleton`, `hlength_setT`, `hlength_itv`,
      `hlength_finite_fin_num`, `hlength_infty_bnd`,
      `hlength_bnd_infty`, `hlength_itv_ge0`, `hlength_Rhull`,
      `le_hlength_itv`, `le_hlength`, `hlength_ge0`, `hlength_semi_additive`,
      `hlength_sigma_sub_additive`, `hlength_sigma_finite`, `lebesgue_measure`
    * `finite_hlengthE` renamed to `finite_hlentgh_itv`
    * `pinfty_hlength` renamed to `infinite_hlength_itv`
  + `lebesgue_measure` now defined with `lebesgue_stieltjes_measure`
  + `lebesgue_measure_itv` does not refer to `hlength` anymore
  + remove one argument of `lebesgue_regularity_inner_sup`

- moved from `lebesgue_measure.v` to `lebesgue_stieltjes_measure.v`
  + notations `_.-ocitv`, `_.-ocitv.-measurable`
  + definitions `ocitv`, `ocitv_display`
  + lemmas `is_ocitv`, `ocitv0`, `ocitvP`, `ocitvD`, `ocitvI`

- in `lebesgue_integral.v`:
  + `integral_dirac` now uses the `\d_` notation
  + order of arguments in the lemma `le_abse_integral`

- in `hoelder.v`:
  + definition `Lnorm` now `HB.lock`ed

- in `probability.v`:
  + `markov` now uses `Num.nneg`

### Renamed

- in `ereal.v`:
  + `le_er_map` -> `le_er_map_in`

- in `sequences.v`:
  + `lim_sup` -> `limn_sup`
  + `lim_inf` -> `limn_inf`
  + `lim_infN` -> `limn_infN`
  + `lim_supE` -> `limn_supE`
  + `lim_infE` -> `limn_infE`
  + `lim_inf_le_lim_sup` -> `limn_inf_sup`
  + `cvg_lim_inf_sup` -> `cvg_limn_inf_sup`
  + `cvg_lim_supE` -> `cvg_limn_supE`
  + `le_lim_supD` -> `le_limn_supD`
  + `le_lim_infD` -> `le_limn_infD`
  + `lim_supD` -> `limn_supD`
  + `lim_infD` -> `limn_infD`
  + `LimSup.lim_esup` -> `limn_esup`
  + `LimSup.lim_einf` -> `limn_einf`
  + `lim_einf_shift` -> `limn_einf_shift`
  + `lim_esup_le_cvg` -> `limn_esup_le_cvg`
  + `lim_einfN` -> `limn_einfN`
  + `lim_esupN` -> `limn_esupN`
  + `lim_einf_sup` -> `limn_einf_sup`
  + `cvgNy_lim_einf_sup` -> `cvgNy_limn_einf_sup`
  + `cvg_lim_einf_sup` -> `cvg_limn_einf_sup`
  + `is_cvg_lim_einfE` -> `is_cvg_limn_einfE`
  + `is_cvg_lim_esupE` -> `is_cvg_limn_esupE`
  + `ereal_nondecreasing_cvg` -> `ereal_nondecreasing_cvgn`
  + `ereal_nondecreasing_is_cvg` -> `ereal_nondecreasing_is_cvgn`
  + `ereal_nonincreasing_cvg` -> `ereal_nonincreasing_cvgn`
  + `ereal_nonincreasing_is_cvg` -> `ereal_nonincreasing_is_cvgn`
  + `ereal_nondecreasing_opp` -> `ereal_nondecreasing_oppn`
  + `nonincreasing_cvg_ge` -> `nonincreasing_cvgn_ge`
  + `nondecreasing_cvg_le` -> `nondecreasing_cvgn_le`
  + `nonincreasing_cvg` -> `nonincreasing_cvgn`
  + `nondecreasing_cvg` -> `nondecreasing_cvgn`
  + `nonincreasing_is_cvg` -> `nonincreasing_is_cvgn`
  + `nondecreasing_is_cvg` -> `nondecreasing_is_cvgn`
  + `near_nonincreasing_is_cvg` -> `near_nonincreasing_is_cvgn`
  + `near_nondecreasing_is_cvg` -> `near_nondecreasing_is_cvgn`
  + `nondecreasing_dvg_lt` -> `nondecreasing_dvgn_lt`

- in `lebesgue_measure.v`:
  + `measurable_fun_lim_sup` -> `measurable_fun_limn_sup`
  + `measurable_fun_lim_esup` -> `measurable_fun_limn_esup`

- in `charge.v`
  + `isCharge` -> `isSemiSigmaAdditive`

### Generalized

- in `classical_sets.v`:
  + `set_nil` generalized to `eqType`

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

- in `lebesgue_integral.v`:
  + weaken an hypothesis of `integral_ae_eq`

### Removed

- `lebesgue_measure_unique` (generalized to `lebesgue_stieltjes_measure_unique`)

- in `sequences.v`:
  + notations `elim_sup`, `elim_inf`
  + `LimSup.lim_esup`, `LimSup.lim_einf`
  + `elim_inf_shift`
  + `elim_sup_le_cvg`
  + `elim_infN`
  + `elim_supN`
  + `elim_inf_sup`
  + `cvg_ninfty_elim_inf_sup`
  + `cvg_ninfty_einfs`
  + `cvg_ninfty_esups`
  + `cvg_pinfty_einfs`
  + `cvg_pinfty_esups`
  + `cvg_elim_inf_sup`
  + `is_cvg_elim_infE`
  + `is_cvg_elim_supE`

- in `lebesgue_measure.v`:
  + `measurable_fun_elim_sup`

## [0.6.5] - 2023-10-02

### Added

- in `mathcomp_extra.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq`
  + lemma `gerBl`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `ereal.v`:
  + lemmas `uboundT`, `supremumsT`, `supremumT`, `ereal_supT`, `range_oppe`,
    `ereal_infT`
- in `constructive_ereal.v`:
  + lemma `eqe_pdivr_mull`
  + lemma `bigmaxe_fin_num`
- in file `topology.v`,
  + definition `regular_space`.
  + lemma `ent_closure`.
- in `normedtype.v`:
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`
  + new lemmas `normal_openP`, `uniform_regular`,
    `regular_openP`, and `pseudometric_normal`.
- in `sequences.v`:
  + lemma `cvge_harmonic`
- in `convex.v`:
  + lemmas `conv_gt0`, `convRE`
  + definition `convex_function`
- in `exp.v`:
  + lemmas `concave_ln`, `conjugate_powR`
  + lemmas `ln_le0`, `ger_powR`, `ler1_powR`, `le1r_powR`, `ger1_powR`,
    `ge1r_powR`, `ge1r_powRZ`, `le1r_powRZ`
  + lemma `gt0_ltr_powR`
  + lemma `powR_injective`
- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`
  + definition `ess_sup`, lemma `ess_sup_ge0`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`
  + lemma `measurable_ball`
  + lemma `measurable_mulrr`
- in `lebesgue_integral.v`,
  + new lemmas `integral_le_bound`, `continuous_compact_integrable`, and
    `lebesgue_differentiation_continuous`.
  + new lemmas `simple_bounded`, `measurable_bounded_integrable`,
    `compact_finite_measure`, `approximation_continuous_integrable`
  + lemma `ge0_integral_count`
- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- new file `hoelder.v`:
  + definition `Lnorm`, notations `'N[mu]_p[f]`, `'N_p[f]`
  + lemmas `Lnorm1`, `Lnorm_ge0`, `eq_Lnorm`, `Lnorm_eq0_eq0`
  + lemma `hoelder`
  + lemmas `Lnorm_counting`, `hoelder2`, `convex_powR`

### Changed

- in `cardinality.v`:
  + implicits of `fimfunP`
- in `constructive_ereal.v`:
  + `lee_adde` renamed to `lee_addgt0Pr` and turned into a reflect
  + `lee_dadde` renamed to `lee_daddgt0Pr` and turned into a reflect
- in `exp.v`:
  + `gt0_ler_powR` now uses `Num.nneg`
- removed dependency in `Rstruct.v` on `normedtype.v`:
- added dependency in `normedtype.v` on `Rstruct.v`:
- `mnormalize` moved from `kernel.v` to `measure.v` and generalized
- in `measure.v`:
  + implicits of `measurable_fst` and `measurable_snd`
- in `lebesgue_integral.v`
  + rewrote `negligible_integral` to replace the positivity condition
    with an integrability condition, and added `ge0_negligible_integral`.
  + implicits of `integral_le_bound`

### Renamed

- in `constructive_ereal.v`:
  + `lee_opp` -> `leeN2`
  + `lte_opp` -> `lteN2`
- in `normedtype.v`:
  + `normal_urysohnP` -> `normal_separatorP`.
- in `exp.v`:
  + `gt0_ler_powR` -> `ge0_ler_powR`

### Removed

- in `signed.v`:
  + specific notation for `2%:R`,
    now subsumed by number notations in MC >= 1.15
    Note that when importing ssrint, `2` now denotes `2%:~R` rather than `2%:R`,
    which are convertible but don't have the same head constant.

## [0.6.4] - 2023-08-05

### Added

- in `theories/Make`
  + file `probability.v` (wasn't compiled in OPAM packages up to now)
- in `mathcomp_extra.v`:
  + definition `min_fun`, notation `\min`
  + new lemmas `maxr_absE`, `minr_absE`
- in file `boolp.v`,
  + lemmas `notP`, `notE`
  + new lemma `implyE`.
  + new lemmas `contra_leP` and `contra_ltP`
- in `classical_sets.v`:
  + lemmas `set_predC`, `preimage_true`, `preimage_false`
  + lemmas `properW`, `properxx`
  + lemma `Zorn_bigcup`
  + lemmas `imsub1` and `imsub1P`
  + lemma `bigcup_bigcup`
- in `constructive_ereal.v`:
  + lemmas `lte_pmulr`, `lte_pmull`, `lte_nmulr`, `lte_nmull`
  + lemmas `lte0n`, `lee0n`, `lte1n`, `lee1n`
  + lemmas `fine0` and `fine1`
- in file `reals.v`:
  + lemmas `sup_sumE`, `inf_sumE`
- in `signed.v`:
  + lemmas `Posz_snum_subproof` and `Negz_snum_subproof`
  + canonical instances `Posz_snum` and `Negz_snum`
- in file `topology.v`,
  + new lemma `uniform_nbhsT`.
  + definition `set_nbhs`.
  + new lemmas `filterI_iter_sub`, `filterI_iterE`, `finI_fromI`,
    `filterI_iter_finI`, `smallest_filter_finI`, and `set_nbhsP`.
  + lemma `bigsetU_compact`
  + lemma `ball_symE`
  + new lemma `pointwise_cvgP`.
  + lemma `closed_bigcup`
  + definition `normal_space`.
  + new lemmas `filter_inv`, and `countable_uniform_bounded`.
- in file `normedtype.v`,
  + definition `edist`.
  + lemmas `edist_ge0`, `edist_neqNy`, `edist_lt_ball`,
    `edist_fin`, `edist_pinftyP`, `edist_finP`, `edist_fin_open`,
    `edist_fin_closed`, `edist_pinfty_open`, `edist_sym`, `edist_triangle`,
    `edist_continuous`, `edist_closeP`, and `edist_refl`.
  + definitions `edist_inf`, `uniform_separator`, and `Urysohn`.
  + lemmas `continuous_min`, `continuous_max`, `edist_closel`,
    `edist_inf_ge0`, `edist_inf_neqNy`, `edist_inf_triangle`,
    `edist_inf_continuous`, `edist_inf0`, `Urysohn_continuous`,
    `Urysohn_range`, `Urysohn_sub0`, `Urysohn_sub1`, `Urysohn_eq0`,
    `Urysohn_eq1`, `uniform_separatorW`, `normal_uniform_separator`,
    `uniform_separatorP`, `normal_urysohnP`, and
    `subset_closure_half`.
- in file `real_interval.v`,
  + new lemma `bigcup_itvT`.
- in `sequences.v`:
  + lemma `eseries_cond`
  + lemmas `eseries_mkcondl`, `eseries_mkcondr`
  + new lemmas `geometric_partial_tail`, and `geometric_le_lim`.
- in `exp.v`:
  + lemmas `powRrM`, `gt0_ler_powR`,
    `gt0_powR`, `norm_powR`, `lt0_norm_powR`,
    `powRB`
  + lemmas `poweRrM`, `poweRAC`, `gt0_poweR`,
    `poweR_eqy`, `eqy_poweR`, `poweRD`, `poweRB`
  + notation `` e `^?(r +? s) ``
  + lemmas `expR_eq0`, `powRN`
  + definition `poweRD_def`
  + lemmas `poweRD_defE`, `poweRB_defE`, `add_neq0_poweRD_def`,
    `add_neq0_poweRB_def`, `nneg_neq0_poweRD_def`, `nneg_neq0_poweRB_def`
  + lemmas `powR_eq0`, `poweR_eq0`
- in file `numfun.v`,
  + new lemma `continuous_bounded_extension`.
- in `measure.v`:
  + lemma `lebesgue_regularity_outer`
  + new lemmas `measureU0`, `nonincreasing_cvg_mu`, and `epsilon_trick0`.
  + new lemmas `finite_card_sum`, and `measureU2`.
- in `lebesgue_measure.v`:
  + lemma `closed_measurable`
  + new lemmas `lebesgue_nearly_bounded`, and `lebesgue_regularity_inner`.
  + new lemmas `pointwise_almost_uniform`, and
    `ae_pointwise_almost_uniform`.
  + lemmas `measurable_fun_ltr`, `measurable_minr`
- in file `lebesgue_integral.v`,
  + new lemmas `lusin_simple`, and `measurable_almost_continuous`.
  + new lemma `approximation_sfun_integrable`.

### Changed

- in `classical_sets.v`:
  + `bigcup_bigcup_dep` renamed to `bigcup_setM_dep` and
    equality in the statement reversed
  + `bigcup_bigcup` renamed to `bigcup_setM` and
    equality in the statement reversed
- in `sequences.v`:
  + lemma `nneseriesrM` generalized and renamed to `nneseriesZl`
- in `exp.v`:
  + lemmas `power_posD` (now `powRD`), `power_posB` (now `powRB`)

- moved from `lebesgue_measure.v` to `real_interval.v`:
  + lemmas `set1_bigcap_oc`, `itv_bnd_open_bigcup`, `itv_open_bnd_bigcup`,
    `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`
- moved from `functions.v` to `classical_sets.v`: `subsetP`.
- moved from `normedtype.v` to `topology.v`: `Rhausdorff`.

### Renamed

- in `boolp.v`:
  + `mextentionality` -> `mextensionality`
  + `extentionality` -> `extensionality`
- in `classical_sets.v`:
  + `bigcup_set_cond` -> `bigcup_seq_cond`
  + `bigcup_set` -> `bigcup_seq`
  + `bigcap_set_cond` -> `bigcap_seq_cond`
  + `bigcap_set` -> `bigcap_seq`
- in `normedtype.v`:
  + `nbhs_closedballP` -> `nbhs_closed_ballP`
- in `exp.v`:
  + `expK` -> `expRK`
  + `power_pos_eq0` -> `powR_eq0_eq0`
  + `power_pos_inv` -> `powR_invn`
  + `powere_pos_eq0` -> `poweR_eq0_eq0`
  + `power_pos` -> `powR`
  + `power_pos_ge0` -> `powR_ge0`
  + `power_pos_gt0` -> `powR_gt0`
  + `gt0_power_pos` -> `gt0_powR`
  + `power_pos0` -> `powR0`
  + `power_posr1` -> `powRr1`
  + `power_posr0` -> `powRr0`
  + `power_pos1` -> `powR1`
  + `ler_power_pos` -> `ler_powR`
  + `gt0_ler_power_pos` -> `gt0_ler_powR`
  + `power_posM` -> `powRM`
  + `power_posrM` -> `powRrM`
  + `power_posAC` -> `powRAC`
  + `power_posD` -> `powRD`
  + `power_posN` -> `powRN`
  + `power_posB` -> `powRB`
  + `power_pos_mulrn` -> `powR_mulrn`
  + `power_pos_inv1` -> `powR_inv1`
  + `power_pos_intmul` -> `powR_intmul`
  + `ln_power_pos` -> `ln_powR`
  + `power12_sqrt` -> `powR12_sqrt`
  + `norm_power_pos` -> `norm_powR`
  + `lt0_norm_power_pos` -> `lt0_norm_powR`
  + `powere_pos` -> `poweR`
  + `powere_pos_EFin` -> `poweR_EFin`
  + `powere_posyr` -> `poweRyr`
  + `powere_pose0` -> `poweRe0`
  + `powere_pose1` -> `poweRe1`
  + `powere_posNyr` -> `poweRNyr`
  + `powere_pos0r` -> `poweR0r`
  + `powere_pos1r` -> `poweR1r`
  + `fine_powere_pos` -> `fine_poweR`
  + `powere_pos_ge0` -> `poweR_ge0`
  + `powere_pos_gt0` -> `poweR_gt0`
  + `powere_posM` -> `poweRM`
  + `powere12_sqrt` -> `poweR12_sqrt`
- in `lebesgue_measure.v`:
  + `measurable_power_pos` -> `measurable_powR`
- in `lebesgue_integral.v`:
  + `ge0_integralM_EFin` -> `ge0_integralZl_EFin`
  + `ge0_integralM` -> `ge0_integralZl`
  + `integralM_indic` -> `integralZl_indic`
  + `integralM_indic_nnsfun` -> `integralZl_indic_nnsfun`
  + `integrablerM` -> `integrableZl`
  + `integrableMr` -> `integrableZr`
  + `integralM` -> `integralZl`

### Generalized

- in `sequences.v`:
  + lemmas `is_cvg_nneseries_cond`, `is_cvg_npeseries_cond`
  + lemmas `is_cvg_nneseries`, `is_cvg_npeseries`
  + lemmas `nneseries_ge0`, `npeseries_le0`
  + lemmas `eq_eseriesr`, `lee_nneseries`
- in `exp.v`:
  + lemmas `convex_expR`, `ler_power_pos` (now `ler_powR`)
  + lemma `ln_power_pos` (now `ln_powR`)
  + lemma `ln_power_pos`
- in `measure.v`:
  + lemmas `measureDI`, `measureD`, `measureUfinl`, `measureUfinr`,
    `null_set_setU`, `measureU0`
    (from measure to content)
  + lemma `subset_measure0` (from `realType` to `realFieldType`)
- in file `lebesgue_integral.v`, updated `le_approx`.

### Removed

- in `topology.v`:
  + lemma `my_ball_le` (use `ball_le` instead)
- in `signed.v`:
  + lemma `nat_snum_subproof`
  + canonical instance `nat_snum` (useless, there is already a default instance
    pointing to the typ_snum mechanism (then identifying nats as >= 0))

## [0.6.3] - 2023-06-21

### Added

- in `mathcomp_extra.v`
  + definition `coefE` (will be in MC 2.1/1.18)
  + lemmas `deg2_poly_canonical`, `deg2_poly_factor`, `deg2_poly_min`,
    `deg2_poly_minE`, `deg2_poly_ge0`, `Real.deg2_poly_factor`,
    `deg_le2_poly_delta_ge0`, `deg_le2_poly_ge0`
    (will be in MC 2.1/1.18)
  + lemma `deg_le2_ge0`
- in `classical_sets.v`:
  + lemmas `set_eq_le`, `set_neq_lt`,
  + new lemma `trivIset1`.
  + lemmas `preimage_mem_true`, `preimage_mem_false`
- in `functions.v`:
  + lemma `sumrfctE`
- in `set_interval.v`:
  + lemma `set_lte_bigcup`
- in `topology.v`:
  + lemma `globally0`
  + definitions `basis`, and `second_countable`.
  + lemmas `clopen_countable` and `compact_countable_base`.
- in `ereal.v`:
  + lemmas `compreDr`, `compreN`
- in `constructive_ereal.v`:
  + lemmas `lee_sqr`, `lte_sqr`, `lee_sqrE`, `lte_sqrE`, `sqre_ge0`,
    `EFin_expe`, `sqreD`, `sqredD`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`
- in `sequences.v`:
  + lemma `eq_eseriesl`
- in `measure.v`:
  + new lemmas `measurable_subring`, and `semiring_sigma_additive`.
  + added factory `Content_SubSigmaAdditive_isMeasure`
  + lemma `measurable_fun_bigcup`
  + definition `measure_dominates`, notation `` `<< ``
  + lemma `measure_dominates_trans`
  + defintion `mfrestr`
  + lemmas `measurable_pair1`, `measurable_pair2`
- in `lebesgue_measure.v`:
  + lemma `measurable_expR`
- in `lebesgue_integral.v`:
  + lemmas `emeasurable_fun_lt`, `emeasurable_fun_le`, `emeasurable_fun_eq`,
    `emeasurable_fun_neq`
  + lemma `integral_ae_eq`
  + lemma `integrable_sum`
  + lemmas `integrableP`, `measurable_int`
- in file `kernel.v`,
  + definitions `kseries`, `measure_fam_uub`, `kzero`, `kdirac`,
    `prob_pointed`, `mset`, `pset`, `pprobability`, `kprobability`, `kadd`,
    `mnormalize`, `knormalize`, `kcomp`, and `mkcomp`.
  + lemmas `eq_kernel`, `measurable_fun_kseries`, `integral_kseries`,
    `measure_fam_uubP`, `eq_sfkernel`, `kzero_uub`,
    `sfinite_kernel`, `sfinite_kernel_measure`, `finite_kernel_measure`,
    `measurable_prod_subset_xsection_kernel`,
    `measurable_fun_xsection_finite_kernel`,
    `measurable_fun_xsection_integral`,
    `measurable_fun_integral_finite_kernel`,
    `measurable_fun_integral_sfinite_kernel`, `lt0_mset`, `gt1_mset`,
    `kernel_measurable_eq_cst`, `kernel_measurable_neq_cst`, `kernel_measurable_fun_eq_cst`,
    `measurable_fun_kcomp_finite`, `mkcomp_sfinite`,
    `measurable_fun_mkcomp_sfinite`, `measurable_fun_preimage_integral`,
    `measurable_fun_integral_kernel`, and `integral_kcomp`.
  + lemma `measurable_fun_mnormalize`
- in `probability.v`
  + definition of `covariance`
  + lemmas `expectation_sum`, `covarianceE`, `covarianceC`,
    `covariance_fin_num`, `covariance_cst_l`, `covariance_cst_r`,
    `covarianceZl`, `covarianceZr`, `covarianceNl`, `covarianceNr`,
    `covarianceNN`, `covarianceDl`, `covarianceDr`, `covarianceBl`,
    `covarianceBr`, `variance_fin_num`, `varianceZ`, `varianceN`,
    `varianceD`, `varianceB`, `varianceD_cst_l`, `varianceD_cst_r`,
    `varianceB_cst_l`, `varianceB_cst_r`
  + lemma `covariance_le`
  + lemma `cantelli`
- in `charge.v`:
  + definition `measure_of_charge`
  + definition `crestr0`
  + definitions `jordan_neg`, `jordan_pos`
  + lemmas `jordan_decomp`, `jordan_pos_dominates`, `jordan_neg_dominates`
  + lemma `radon_nikodym_finite`
  + definition `Radon_Nikodym`, notation `'d nu '/d mu`
  + theorems `Radon_Nikodym_integrable`, `Radon_Nikodym_integral`

### Changed

- in `lebesgue_measure.v`
  + `measurable_funrM`, `measurable_funN`, `measurable_fun_exprn`
- in `lebesgue_integral.v`:
  + lemma `xsection_ndseq_closed` generalized from a measure to a family of measures
  + locked `integrable` and put it in bool rather than Prop
- in `probability.v`
  + `variance` is now defined based on `covariance`

### Renamed

- in `derive.v`:
  + `Rmult_rev` -> `mulr_rev`
  + `rev_Rmult` -> `rev_mulr`
  + `Rmult_is_linear` -> `mulr_is_linear`
  + `Rmult_linear` -> `mulr_linear`
  + `Rmult_rev_is_linear` -> `mulr_rev_is_linear`
  + `Rmult_rev_linear` -> `mulr_rev_linear`
  + `Rmult_bilinear` -> `mulr_bilinear`
  + `is_diff_Rmult` -> `is_diff_mulr`
- in `measure.v`:
  + `measurable_fun_id` -> `measurable_id`
  + `measurable_fun_cst` -> `measurable_cst`
  + `measurable_fun_comp` -> `measurable_comp`
  + `measurable_funT_comp` -> `measurableT_comp`
  + `measurable_fun_fst` -> `measurable_fst`
  + `measurable_fun_snd` -> `measurable_snd`
  + `measurable_fun_swap` -> `measurable_swap`
  + `measurable_fun_pair` -> `measurable_fun_prod`
  + `isMeasure0` -> ``Content_isMeasure`
  + `Hahn_ext` -> `measure_extension`
  + `Hahn_ext_ge0` -> `measure_extension_ge0`
  + `Hahn_ext_sigma_additive` -> `measure_extension_semi_sigma_additive`
  + `Hahn_ext_unique` -> `measure_extension_unique`
  + `RingOfSets_from_semiRingOfSets` -> `SemiRingOfSets_isRingOfSets`
  + `AlgebraOfSets_from_RingOfSets` -> `RingOfSets_isAlgebraOfSets`
  + `Measurable_from_algebraOfSets` -> `AlgebraOfSets_isMeasurable`
  + `ring_sigma_additive` -> `ring_semi_sigma_additive`
- in `lebesgue_measure.v`
  + `measurable_funN` -> `measurable_oppr`
  + `emeasurable_fun_minus` -> `measurable_oppe`
  + `measurable_fun_abse` -> `measurable_abse`
  + `measurable_EFin` -> `measurable_image_EFin`
  + `measurable_fun_EFin` -> `measurable_EFin`
  + `measurable_fine` -> `measurable_image_fine`
  + `measurable_fun_fine` -> `measurable_fine`
  + `measurable_fun_normr` -> `measurable_normr`
  + `measurable_fun_exprn` -> `measurable_exprn`
  + `emeasurable_fun_max` -> `measurable_maxe`
  + `emeasurable_fun_min` -> `measurable_mine`
  + `measurable_fun_max` -> `measurable_maxr`
  + `measurable_fun_er_map` -> `measurable_er_map`
  + `emeasurable_fun_funepos` -> `measurable_funepos`
  + `emeasurable_fun_funeneg` -> `measurable_funeneg`
  + `measurable_funrM` -> `measurable_mulrl`
- in `lebesgue_integral.v`:
  + `measurable_fun_indic` -> `measurable_indic`

### Deprecated

- in `lebesgue_measure.v`:
  + lemma `measurable_fun_sqr` (use `measurable_exprn` instead)
  + lemma `measurable_fun_opp` (use `measurable_oppr` instead)

### Removed

- in `normedtype.v`:
  + instance `Proper_dnbhs_realType`
- in `measure.v`:
  + instances `ae_filter_algebraOfSetsType`, `ae_filter_measurableType`,
  `ae_properfilter_measurableType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_funN` (use `measurableT_comp`) instead
  + lemma `measurable_fun_prod1` (use `measurableT_comp` instead)
  + lemma `measurable_fun_prod2` (use `measurableT_comp` instead)
- in `lebesgue_integral.v`
  + lemma `emeasurable_funN` (was already in `lebesgue_measure.v`, use `measurableT_comp` instead)

## [0.6.2] - 2023-04-21

### Added

- in `mathcomp_extra.v`:
  + lemma `ler_sqrt`
  + lemma `lt_min_lt`
- in `classical_sets.v`:
  + lemmas `ltn_trivIset`, `subsetC_trivIset`
- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
  + lemmas `EFin_min`, `EFin_max`
  + definition `sqrte`
  + lemmas `sqrte0`, `sqrte_ge0`, `lee_sqrt`, `sqrteM`, `sqr_sqrte`,
    `sqrte_sqr`, `sqrte_fin_num`
- in `ereal.v`:
  + lemmas `compreBr`, `compre_scale`
  + lemma `le_er_map`
- in `set_interval.v`:
  + lemma `onem_factor`
  + lemmas `in1_subset_itv`, `subset_itvW`
- in `topology.v`,
  + definitions `totally_disconnected`, and `zero_dimensional`.
  + lemmas `component_closed`, `zero_dimension_prod`,
    `discrete_zero_dimension`, `zero_dimension_totally_disconnected`,
    `totally_disconnected_cvg`, and `totally_disconnected_prod`.
  + definitions `split_sym`, `gauge`, `gauge_uniformType_mixin`,
    `gauge_topologicalTypeMixin`, `gauge_filtered`, `gauge_topologicalType`,
    `gauge_uniformType`, `gauge_pseudoMetric_mixin`, and
    `gauge_pseudoMetricType`.
  + lemmas `iter_split_ent`, `gauge_ent`, `gauge_filter`,
    `gauge_refl`, `gauge_inv`, `gauge_split`, `gauge_countable_uniformity`, and
    `uniform_pseudometric_sup`.
  + definitions `discrete_ent`, `discrete_uniformType`, `discrete_ball`,
    `discrete_pseudoMetricType`, and `pseudoMetric_bool`.
  + lemmas `finite_compact`, `discrete_ball_center`, `compact_cauchy_cvg`
- in `normedtype.v`:
  + lemmas `cvg_at_right_filter`, `cvg_at_left_filter`,
    `cvg_at_right_within`, `cvg_at_left_within`
- in `sequences.v`:
  + lemma `seqDUIE`
- in `derive.v`:
  + lemma `derivable_within_continuous`
- in `realfun.v`:
  + definition `derivable_oo_continuous_bnd`, lemma `derivable_oo_continuous_bnd_within`
- in `exp.v`:
  + lemma `ln_power_pos`
  + definition `powere_pos`, notation ``` _ `^ _ ``` in `ereal_scope`
  + lemmas `powere_pos_EFin`, `powere_posyr`, `powere_pose0`,
    `powere_pose1`, `powere_posNyr` `powere_pos0r`, `powere_pos1r`,
    `powere_posNyr`, `fine_powere_pos`, `powere_pos_ge0`,
    `powere_pos_gt0`, `powere_pos_eq0`, `powere_posM`, `powere12_sqrt`
  + lemmas `derive_expR`, `convex_expR`
  + lemmas `power_pos_ge0`, `power_pos0`, `power_pos_eq0`,
    `power_posM`, `power_posAC`, `power12_sqrt`, `power_pos_inv1`,
    `power_pos_inv`, `power_pos_intmul`
- in `measure.v`:
  + lemmas `negligibleU`, `negligibleS`
  + definition `almost_everywhere_notation`
  + instances `ae_filter_ringOfSetsType`, `ae_filter_algebraOfSetsType`,
    `ae_filter_measurableType`
  + instances `ae_properfilter_algebraOfSetsType`, `ae_properfilter_measurableType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_itv`
  + lemma `measurable_fun_er_map`
  + lemmas `measurable_fun_ln`, `measurable_fun_power_pos`
- in `lebesgue_integral.v`:
  + lemma `sfinite_Fubini`
  + instance of `isMeasurableFun` for `normr`
  + lemma `finite_measure_integrable_cst`
  + lemma `ae_ge0_le_integral`
  + lemma `ae_eq_refl`
- new file `convex.v`:
  + mixin `isConvexSpace`, structure `ConvexSpace`, notations `convType`,
    `_ <| _ |> _`
  + lemmas `conv1`, `second_derivative_convex`
- new file `charge.v`:
  + mixin `isAdditiveCharge`, structure `AdditiveCharge`, notations
    `additive_charge`, `{additive_charge set T -> \bar R}`
  + mixin `isCharge`, structure `Charge`, notations `charge`,
    `{charge set T -> \bar R}`
  + lemmas `charge0`, `charge_semi_additiveW`, `charge_semi_additive2E`,
    `charge_semi_additive2`, `chargeU`, `chargeDI`, `chargeD`,
    `charge_partition`
  + definitions `crestr`, `cszero`, `cscale`, `positive_set`, `negative_set`
  + lemmas `negative_set_charge_le0`, `negative_set0`, `bigcup_negative_set`,
    `negative_setU`, `positive_negative0`
  + definition `hahn_decomposition`
  + lemmas `hahn_decomposition_lemma`, `Hahn_decomposition`, `Hahn_decomposition_uniq`
- new file `itv.v`:
  + definition `wider_itv`
  + module `Itv`:
    * definitions `map_itv_bound`, `map_itv`
    * lemmas `le_map_itv_bound`, `subitv_map_itv`
    * definition `itv_cond`
    * record `def`
    * notation `spec`
    * record `typ`
    * definitions `mk`, `from`, `fromP`
  + notations `{itv R & i}`, `{i01 R}`, `%:itv`, `[itv of _]`, `inum`, `%:inum`
  + definitions `itv_eqMixin`, `itv_choiceMixin`, `itv_porderMixin`
  + canonical `itv_subType`, `itv_eqType`, `itv_choiceType`, `itv_porderType`
  + lemma `itv_top_typ_subproof`
  + canonical `itv_top_typ`
  + lemma `typ_inum_subproof`
  + canonical `typ_inum`
  + notation `unify_itv`
  + lemma `itv_intro`
  + definition `empty_itv`
  + lemmas `itv_bottom`, `itv_gt0`, `itv_le0F`, `itv_lt0`, `itv_ge0F`,
    `itv_ge0`, `lt0F`, `le0`, `gt0F`, `lt1`, `ge1F`, `le1`, `gt1F`
  + lemma `widen_itv_subproof`
  + definition `widen_itv`
  + lemma `widen_itvE`
  + notation `%:i01`
  + lemma `zero_inum_subproof`
  + canonical `zero_inum`
  + lemma `one_inum_subproof`
  + canonical `one_inum`
  + definition `opp_itv_bound_subdef`
  + lemmas `opp_itv_ge0_subproof`, `opp_itv_gt0_subproof`, `opp_itv_boundr_subproof`,
    `opp_itv_le0_subproof`, `opp_itv_lt0_subproof`, `opp_itv_boundl_subproof`
  + definition `opp_itv_subdef`
  + lemma `opp_inum_subproof `
  + canonical `opp_inum`
  + definitions `add_itv_boundl_subdef`, `add_itv_boundr_subdef`, `add_itv_subdef`
  + lemma `add_inum_subproof`
  + canonical `add_inum`
  + definitions `itv_bound_signl`, `itv_bound_signr`, `interval_sign`
  + variant `interval_sign_spec`
  + lemma `interval_signP`
  + definitions `mul_itv_boundl_subdef`, `mul_itv_boundr_subdef`
  + lemmas `mul_itv_boundl_subproof`, `mul_itv_boundrC_subproof`, `mul_itv_boundr_subproof`,
    `mul_itv_boundr'_subproof`
  + definition `mul_itv_subdef`
  + lemmas `map_itv_bound_min`, `map_itv_bound_max`, `mul_inum_subproof`
  + canonical `mul_inum`
  + lemmas `inum_eq`, `inum_le`, `inum_lt`
- new file `probability.v`:
  + definition `random_variable`, notation `{RV _ >-> _}`
  + lemmas `notin_range_measure`, `probability_range`
  + definition `distribution`, instance of `isProbability`
  + lemma `probability_distribution`, `integral_distribution`
  + definition `expectation`, notation `'E_P[X]`
  + lemmas `expectation_cst`, `expectation_indic`, `integrable_expectation`,
    `expectationM`, `expectation_ge0`, `expectation_le`, `expectationD`,
    `expectationB`
  + definition `variance`, `'V_P[X]`
  + lemma `varianceE`
  + lemmas `variance_ge0`, `variance_cst`
  + lemmas `markov`, `chebyshev`,
  + mixin `MeasurableFun_isDiscrete`, structure `discreteMeasurableFun`,
    notation `{dmfun aT >-> T}`
  + definition `discrete_random_variable`, notation `{dRV _ >-> _}`
  + definitions `dRV_dom_enum`, `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV_enum`, `distribution_dRV`, `sum_enum_prob`,
    `dRV_expectation`
  + definion `pmf`, lemma `expectation_pmf`

### Changed

- in `mathcomp_extra.v`
  + lemmas `eq_bigmax`, `eq_bigmin` changed to respect `P` in the returned type.
- in `constructive_ereal.v`:
  + `maxEFin` changed to `fine_max`
  + `minEFin` changed to `fine_min`
- in `exp.v`:
  + generalize `exp_fun` and rename to `power_pos`
  + `exp_fun_gt0` has now a condition and is renamed to `power_pos_gt0`
  + remove condition of `exp_funr0` and rename to `power_posr0`
  + weaken condition of `exp_funr1` and rename to `power_posr1`
  + weaken condition of `exp_fun_inv` and rename to `power_pos_inv`
  + `exp_fun1` -> `power_pos1`
  + rename `ler_exp_fun` to `ler_power_pos`
  + `exp_funD` -> `power_posD`
  + weaken condition of `exp_fun_mulrn` and rename to `power_pos_mulrn`
  + the notation ``` `^ ``` has now scope `real_scope`
  + weaken condition of `riemannR_gt0` and `dvg_riemannR`
- in `measure.v`:
  + generalize `negligible` to `semiRingOfSetsType`
  + definition `almost_everywhere`

### Renamed

- in `functions.v`:
  + `IsFun` -> `isFun`
- in `set_interval.v`:
  + `conv` -> `line_path`
  + `conv_id` -> `line_path_id`
  + `ndconv` -> `ndline_path`
  + `convEl` -> `line_pathEl`
  + `convEr` -> `line_pathEr`
  + `conv10` -> `line_path10`
  + `conv0` -> `line_path0`
  + `conv1` -> `line_path1`
  + `conv_sym` -> `line_path_sym`
  + `conv_flat` -> `line_path_flat`
  + `leW_conv` -> `leW_line_path`
  + `ndconvE` -> `ndline_pathE`
  + `convK` -> `line_pathK`
  + `conv_inj` -> `line_path_inj`
  + `conv_bij` -> `line_path_bij`
  + `le_conv` -> `le_line_path`
  + `lt_conv` -> `lt_line_path`
  + `conv_itv_bij` -> `line_path_itv_bij`
  + `mem_conv_itv` -> `mem_line_path_itv`
  + `mem_conv_itvcc` -> `mem_line_path_itvcc`
  + `range_conv` -> `range_line_path`
- in `topology.v`:
  + `Topological.ax1` -> `Topological.nbhs_pfilter`
  + `Topological.ax2` -> `Topological.nbhsE`
  + `Topological.ax3` -> `Topological.openE`
  + `entourage_filter` -> `entourage_pfilter`
  + `Uniform.ax1` -> `Uniform.entourage_filter`
  + `Uniform.ax2` -> `Uniform.entourage_refl`
  + `Uniform.ax3` -> `Uniform.entourage_inv`
  + `Uniform.ax4` -> `Uniform.entourage_split_ex`
  + `Uniform.ax5` -> `Uniform.nbhsE`
  + `PseudoMetric.ax1` -> `PseudoMetric.ball_center`
  + `PseudoMetric.ax2` -> `PseudoMetric.ball_sym`
  + `PseudoMetric.ax3` -> `PseudoMetric.ball_triangle`
  + `PseudoMetric.ax4` -> `PseudoMetric.entourageE`
- in `measure.v`:
  + `emeasurable_fun_bool` -> `measurable_fun_bool`
- in `lebesgue_measure.v`:
  + `punct_eitv_bnd_pinfty` -> `punct_eitv_bndy`
  + `punct_eitv_ninfty_bnd` -> `punct_eitv_Nybnd`
  + `eset1_pinfty` -> `eset1y`
  + `eset1_ninfty` -> `eset1Ny`
  + `ErealGenOInfty.measurable_set1_ninfty` -> `ErealGenOInfty.measurable_set1Ny`
  + `ErealGenOInfty.measurable_set1_pinfty` -> `ErealGenOInfty.measurable_set1y`
  + `ErealGenCInfty.measurable_set1_ninfty` -> `ErealGenCInfty.measurable_set1Ny`
  + `ErealGenCInfty.measurable_set1_pinfty` -> `ErealGenCInfty.measurable_set1y`

### Deprecated

- in `realsum.v`:
  + `psumB`, `interchange_sup`, `interchange_psum`
- in `distr.v`:
  + `dlet_lim`, `dlim_let`, `exp_split`, `exp_dlet`,
    `dlet_dlet`, `dmargin_dlet`, `dlet_dmargin`,
    `dfst_dswap`, `dsnd_dswap`, `dsndE`, `pr_dlet`,
    `exp_split`, `exp_dlet`
- in `measure.v`:
  + lemma `measurable_fun_ext`
- in `lebesgue_measure.v`:
  + lemmas `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd`
    (use `emeasurable_itv` instead)

### Removed

- in `lebesgue_integral.v`:
  + lemma `ae_eq_mul`

## [0.6.1] - 2023-02-24

### Added

- in `mathcomp_extra.v`:
  + lemma `add_onemK`
  + function `swap`
- in file `boolp.v`,
  + new lemma `forallp_asboolPn2`.
- in `classical_sets.v`:
  + canonical `unit_pointedType`
  + lemmas `setT0`, `set_unit`, `set_bool`
  + lemmas `xsection_preimage_snd`, `ysection_preimage_fst`
  + lemma `trivIset_mkcond`
  + lemmas `xsectionI`, `ysectionI`
  + lemma `coverE`
  + new lemma `preimage_range`.
- in `constructive_ereal.v`:
  + lemmas `EFin_sum_fine`, `sumeN`
  + lemmas `adde_defDr`, `adde_def_sum`, `fin_num_sumeN`
  + lemma `fin_num_adde_defr`, `adde_defN`
  + lemma `oppe_inj`
  + lemmas `expeS`, `fin_numX`
  + lemmas `adde_def_doppeD`, `adde_def_doppeB`
  + lemma `fin_num_sume_distrr`
- in `functions.v`:
  + lemma `countable_bijP`
  + lemma `patchE`
- in `numfun.v`:
  + lemmas `xsection_indic`, `ysection_indic`
- in file `topology.v`,
  + definition `perfect_set`.
  + lemmas `perfectTP`, `perfect_prod`, and `perfect_diagonal`.
  + definitions `countable_uniformity`, `countable_uniformityT`,
    `sup_pseudoMetric_mixin`, `sup_pseudoMetricType`, and
    `product_pseudoMetricType`.
  + lemmas `countable_uniformityP`, `countable_sup_ent`, and
    `countable_uniformity_metric`.
  + definitions `quotient_topology`, and `quotient_open`.
  + lemmas `pi_continuous`, `quotient_continuous`, and
    `repr_comp_continuous`.
  + definitions `hausdorff_accessible`, `separate_points_from_closed`, and
    `join_product`.
  + lemmas `weak_sep_cvg`, `weak_sep_nbhsE`, `weak_sep_openE`,
    `join_product_continuous`, `join_product_open`, `join_product_inj`, and
    `join_product_weak`.
  + definition `clopen`.
  + lemmas `clopenI`, `clopenU`, `clopenC`, `clopen0`, `clopenT`,
    `clopen_comp`, `connected_closure`, `clopen_separatedP`, and
    `clopen_connectedP`.
  + new lemmas `powerset_filter_fromP` and `compact_cluster_set1`.
- in `exp.v`:
  + lemma `expR_ge0`
- in `measure.v`:
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`
  + structures `sigma_finite_additive_measure` and `sigma_finite_measure`
  + lemmas `measurable_curry`, `measurable_fun_fst`, `measurable_fun_snd`,
    `measurable_fun_swap`, `measurable_fun_pair`, `measurable_fun_if_pair`
  + lemmas `dirac0`, `diracT`
  + lemma `fin_num_fun_sigma_finite`
  + structure `FiniteMeasure`, notation `{finite_measure set _ -> \bar _}`
  + definition `sfinite_measure_def`
  + mixin `Measure_isSFinite_subdef`, structure `SFiniteMeasure`,
    notation `{sfinite_measure set _ -> \bar _}`
  + mixin `SigmaFinite_isFinite` with field `fin_num_measure`, structure `FiniteMeasure`,
    notation `{finite_measure set _ -> \bar _}`
  + lemmas `sfinite_measure_sigma_finite`, `sfinite_mzero`, `sigma_finite_mzero`
  + factory `Measure_isFinite`, `Measure_isSFinite`
  + defintion `sfinite_measure_seq`, lemma `sfinite_measure_seqP`
  + mixin `FiniteMeasure_isSubProbability`, structure `SubProbability`,
    notation `subprobability`
  + factory `Measure_isSubProbability`
  + factory `FiniteMeasure_isSubProbability`
  + factory `Measure_isSigmaFinite`
  + lemmas `fin_num_fun_lty`, `lty_fin_num_fun`
  + definition `fin_num_fun`
  + structure `FinNumFun`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_opp`
- in `lebesgue_integral.v`
  + lemmas `integral0_eq`, `fubini_tonelli`
  + product measures now take `{measure _ -> _}` arguments and their
    theory quantifies over a `{sigma_finite_measure _ -> _}`.
  + notations `\x`, `\x^` for `product_measure1` and `product_measure2`

### Changed

- in `fsbigop.v`:
  + implicits of `eq_fsbigr`
- in file `topology.v`,
  + lemma `compact_near_coveringP`
- in `functions.v`:
  + notation `mem_fun_`
- move from `lebesgue_integral.v` to `classical_sets.v`
  + lemmas `trivIset_preimage1`, `trivIset_preimage1_in`
- move from `lebesgue_integral.v` to `numfun.v`
  + lemmas `fimfunE`, `fimfunEord`, factory `FiniteDecomp`
  + lemmas `fimfun_mulr_closed`
  + canonicals `fimfun_mul`, `fimfun_ring`, `fimfun_ringType`
  + defintion `fimfun_ringMixin`
  + lemmas `fimfunM`, `fimfun1`, `fimfun_prod`, `fimfunX`,
    `indic_fimfun_subproof`.
  + definitions `indic_fimfun`, `scale_fimfun`, `fimfun_comRingMixin`
  + canonical `fimfun_comRingType`
  + lemma `max_fimfun_subproof`
  + mixin `IsNonNegFun`, structure `NonNegFun`, notation `{nnfun _ >-> _}`
- in `measure.v`:
  + order of arguments of `isContent`, `Content`, `measure0`, `isMeasure0`,
    `Measure`, `isSigmaFinite`, `SigmaFiniteContent`, `SigmaFiniteMeasure`

### Renamed

- in `measurable.v`:
  + `measurable_fun_comp` -> `measurable_funT_comp`
- in `numfun.v`:
  + `IsNonNegFun` -> `isNonNegFun`
- in `lebesgue_integral.v`:
  + `IsMeasurableFunP` -> `isMeasurableFun`
- in `measure.v`:
  + `{additive_measure _ -> _}` -> `{content _ -> _}`
  + `isAdditiveMeasure` -> `isContent`
  + `AdditiveMeasure` -> `Content`
  + `additive_measure` -> `content`
  + `additive_measure_snum_subproof` -> `content_snum_subproof`
  + `additive_measure_snum` -> `content_snum`
  + `SigmaFiniteAdditiveMeasure` -> `SigmaFiniteContent`
  + `sigma_finite_additive_measure` -> `sigma_finite_content`
  + `{sigma_finite_additive_measure _ -> _}` -> `{sigma_finite_content _ -> _}`
- in `constructive_ereal.v`:
  + `fin_num_adde_def` -> `fin_num_adde_defl`
  + `oppeD` -> `fin_num_oppeD`
  + `oppeB` -> `fin_num_oppeB`
  + `doppeD` -> `fin_num_doppeD`
  + `doppeB` -> `fin_num_doppeB`
- in `topology.v`:
  + `finSubCover` -> `finite_subset_cover`
- in `sequences.v`:
  + `eq_eseries` -> `eq_eseriesr`
- in `esum.v`:
  + `summable_nneseries_esum` -> `summable_eseries_esum`
  + `summable_nneseries` -> `summable_eseries`

### Generalized

- in `classical_sets.v`:
  + `xsection_preimage_snd`, `ysection_preimage_fst`
- in `constructive_ereal.v`:
  + `oppeD`, `oppeB`
- in `esum.v`:
  + lemma `esum_esum`
- in `measure.v`
  + lemma `measurable_fun_comp`
  + lemma `measure_bigcup` generalized,
  + lemma `eq_measure`
  + `sigma_finite` generalized from `numFieldType` to `numDomainType`
  + `fin_num_fun_sigma_finite` generalized from `measurableType` to `algebraOfSetsType`
- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`
  + lemma `integrable_abse`

### Removed

- in `esum.v`:
  + lemma `fsbig_esum`

## [0.6.0] - 2022-12-14

### Added

- OPAM package `coq-mathcomp-classical` containing `boolp.v`
- file `all_classical.v`
- file `classical/set_interval.v`
- in `mathcomp_extra.v`
  + lemma `lez_abs2n`
  + lemmas `pred_oappE` and `pred_oapp_set` (from `classical_sets.v`)
  + lemma `sumr_le0`
  + new definition `inv_fun`.
  + new lemmas `ler_ltP`, and `real_ltr_distlC`.
  + new definitions `proj`, and `dfwith`.
  + new lemmas `dfwithin`, `dfwithout`, and `dfwithP`.
  + new lemma `projK`
  + generalize lemmas `bigmax_le`, `bigmax_lt`, `lt_bigmin` and
    `le_bigmin` from `finType` to `Type`
  + new definition `oAC` to turn an AC operator `T -> T -> T`,
    into a monoid com_law `option T -> option T -> option T`.
  + new generic lemmas `opACE`, `some_big_AC`, `big_ACE`, `big_undup_AC`,
    `perm_big_AC`, `sub_big`, `sub_big_seq`, `sub_big_seq_cond`,
    `uniq_sub_big`, `uniq_sub_big_cond`, `sub_big_idem`, `sub_big_idem_cond`,
    `sub_in_big`, `le_big_ord`, `subset_big`, `subset_big_cond`,
    `le_big_nat_cond`, `le_big_nat`, and `le_big_ord_cond`,
  + specialization to `bigmax`: `sub_bigmax`, `sub_bigmax_seq`,
    `sub_bigmax_cond`, `sub_in_bigmax`, `le_bigmax_nat`,
    `le_bigmax_nat_cond`, `le_bigmax_ord`, `le_bigmax_ord_cond`,
    `subset_bigmax`, and `subset_bigmax_cond`.
  + specialization to `bigmin`,  `sub_bigmax`, `sub_bigmin_seq`,
    `sub_bigmin_cond`, `sub_in_bigmin`, `le_bigmin_nat`,
    `le_bigmin_nat_cond`, `le_bigmin_ord`, `le_bigmin_ord_cond`,
    `subset_bigmin`, and `subset_bigmin_cond`.
- in `classical_sets.v`
  + lemmas `IIDn`, `IISl`
  + lemmas `set_compose_subset`, `compose_diag`
  + notation `\;` for the composition of relations
  + notations `\bigcup_(i < n) F` and `\bigcap_(i < n) F`
  + new lemmas `eq_image_id`, `subKimage`, `subimageK`, and `eq_imageK`.
  + lemma `bigsetU_sup`
  + lemma `image2_subset`
- in `constructive_ereal.v`
  + lemmas `fine_le`, `fine_lt`, `fine_abse`, `abse_fin_num`
  + lemmas `gte_addl`, `gte_addr`
  + lemmas `gte_daddl`, `gte_daddr`
  + lemma `lte_spadder`, `lte_spaddre`
  + lemma `lte_spdadder`
  + lemma `sum_fine`
  + lemmas `lteN10`, `leeN10`
  + lemmas `le0_fin_numE`
  + lemmas `fine_lt0`, `fine_le0`
  + lemma `fine_lt0E`
  + multi-rules `lteey`, `lteNye`
  + new lemmas `real_ltry`, `real_ltNyr`, `real_leey`, `real_leNye`,
    `fin_real`, `addNye`, `addeNy`, `gt0_muley`, `lt0_muley`, `gt0_muleNy`, and
    `lt0_muleNy`.
  + new lemmas `daddNye`, and `daddeNy`.
  + lemma `lt0e`
  + canonicals `maxe_monoid`, `maxe_comoid`, `mine_monoid`, `mine_comoid`
- in `functions.v`,
  + new lemmas `inv_oppr`, `preimageEoinv`, `preimageEinv`, and
    `inv_funK`.
- in `cardinality.v`
  + lemmas `eq_card1`, `card_set1`, `card_eqSP`, `countable_n_subset`,
     `countable_finite_subset`, `eq_card_fset_subset`, `fset_subset_countable`
- in `fsbigop.v`:
  + lemmas `fsumr_ge0`, `fsumr_le0`, `fsumr_gt0`, `fsumr_lt0`, `pfsumr_eq0`,
    `pair_fsbig`, `exchange_fsbig`
  + lemma `fsbig_setU_set1`
- in `ereal.v`:
  + notation `\sum_(_ \in _) _` (from `fsbigop.v`)
  + lemmas `fsume_ge0`, `fsume_le0`, `fsume_gt0`, `fsume_lt0`,
    `pfsume_eq0`, `lee_fsum_nneg_subset`, `lee_fsum`,
    `ge0_mule_fsumr`, `ge0_mule_fsuml` (from `fsbigop.v`)
  + lemmas `finite_supportNe`, `dual_fsumeE`, `dfsume_ge0`, `dfsume_le0`,
    `dfsume_gt0`, `dfsume_lt0`, `pdfsume_eq0`, `le0_mule_dfsumr`, `le0_mule_dfsuml`
  + lemma `fsumEFin`
  + new lemmas `ereal_nbhs_pinfty_gt`, `ereal_nbhs_ninfty_lt`,
    `ereal_nbhs_pinfty_real`, and `ereal_nbhs_ninfty_real`.
- in `classical/set_interval.v`:
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`,
    `disjoint_itv`, `conv`, `factor`, `ndconv` (from `set_interval.v`)
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itv_cc`,
    `set_itvco`, `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`,
    `set_itv_infty_infty`, `set_itv_o_infty`, `set_itv_c_infty`, `set_itv_infty_o`,
    `set_itv_infty_c`, `set_itv_pinfty_bnd`, `set_itv_bnd_ninfty`, `setUitv1`,
    `setU1itv`, `set_itvI`, `neitvE`, `neitvP`, `setitv0`, `has_lbound_itv`,
    `has_ubound_itv`, `hasNlbound`, `hasNubound`, `opp_itv_bnd_infty`,
    `opp_itv_infty_bnd`, `opp_itv_bnd_bnd`, `opp_itvoo`,
    `setCitvl`, `setCitvr`, `set_itv_splitI`, `setCitv`, `set_itv_splitD`,
    `mem_1B_itvcc`, `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`,
    `conv1`, `conv_sym`, `conv_flat`, `leW_conv`, `leW_factor`,
    `factor_flat`, `factorl`, `ndconvE`, `factorr`, `factorK`,
    `convK`, `conv_inj`, `factor_inj`, `conv_bij`, `factor_bij`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`, `conv_itv_bij`,
    `factor_itv_bij`, `mem_conv_itv`, `mem_conv_itvcc`, `range_conv`,
    `range_factor`, `mem_factor_itv`,
    `set_itv_ge`, `trivIset_set_itv_nth`, `disjoint_itvxx`, `lt_disjoint`,
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (from `set_interval.v`)
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (from `reals.v`)
- in `topology.v`:
  + lemmas `continuous_subspaceT`, `subspaceT_continuous`
  + lemma `weak_subspace_open`
  + lemma `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`, `weak_ent_split`,
      `weak_ent_nbhs`
  + definition `map_pair`, `weak_ent`, `weak_uniform_mixin`, `weak_uniformType`
  + lemma `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
      `sup_ent_nbhs`
  + definition `sup_ent`, `sup_uniform_mixin`, `sup_uniformType`
  + definition `product_uniformType`
  + lemma `uniform_entourage`
  + definition `weak_ball`, `weak_pseudoMetricType`
  + lemma `weak_ballE`
  + lemma `finI_from_countable`
  + lemmas `entourage_invI`, `split_ent_subset`
  + definition `countable_uniform_pseudoMetricType_mixin`
  + lemmas `closed_bigsetU`, `accessible_finite_set_closed`
  + new lemmas `eq_cvg`, `eq_is_cvg`, `eq_near`, `cvg_toP`, `cvgNpoint`,
    `filter_imply`, `nbhs_filter`, `near_fun`, `cvgnyPgt`, `cvgnyPgty`,
    `cvgnyPgey`, `fcvg_ballP`, `fcvg_ball`, and `fcvg_ball2P`.
  + new lemmas `dfwith_continuous`, and `proj_open`.
- in `topology.v`, added `near do` and `near=> x do` tactic notations
  to perform some tactics under a `\forall x \near F, ...` quantification.
- in `reals.v`:
  + lemma `floor0`
- in `normedtype.v`,
  + lemmas `closed_ballR_compact` and `locally_compactR`
  + new lemmas `nbhsNimage`, `nbhs_pinfty_real`, `nbhs_ninfty_real`,
    `pinfty_ex_ge`, `cvgryPger`, `cvgryPgtr`, `cvgrNyPler`, `cvgrNyPltr`,
    `cvgry_ger`, `cvgry_gtr`, `cvgrNy_ler`, `cvgrNy_ltr`, `cvgNry`, `cvgNrNy`,
    `cvgry_ge`, `cvgry_gt`, `cvgrNy_le`, `cvgrNy_lt`, `cvgeyPger`, `cvgeyPgtr`,
    `cvgeyPgty`, `cvgeyPgey`, `cvgeNyPler`, `cvgeNyPltr`, `cvgeNyPltNy`,
    `cvgeNyPleNy`, `cvgey_ger`, `cvgey_gtr`, `cvgeNy_ler`, `cvgeNy_ltr`,
    `cvgNey`, `cvgNeNy`, `cvgerNyP`, `cvgeyPge`, `cvgeyPgt`, `cvgeNyPle`,
    `cvgeNyPlt`, `cvgey_ge`, `cvgey_gt`, `cvgeNy_le`, `cvgeNy_lt`, `cvgenyP`,
    `normfZV`, `fcvgrPdist_lt`, `cvgrPdist_lt`, `cvgrPdistC_lt`,
    `cvgr_dist_lt`, `cvgr_distC_lt`, `cvgr_dist_le`, `cvgr_distC_le`,
    `nbhs_norm0P`, `cvgr0Pnorm_lt`, `cvgr0_norm_lt`, `cvgr0_norm_le`, `nbhsDl`,
    `nbhsDr`, `nbhs0P`, `nbhs_right0P`, `nbhs_left0P`, `nbhs_right_gt`,
    `nbhs_left_lt`, `nbhs_right_neq`, `nbhs_left_neq`, `nbhs_right_ge`,
    `nbhs_left_le`, `nbhs_right_lt`, `nbhs_right_le`, `nbhs_left_gt`,
    `nbhs_left_ge`, `nbhsr0P`, `cvgrPdist_le`, `cvgrPdist_ltp`,
    `cvgrPdist_lep`, `cvgrPdistC_le`, `cvgrPdistC_ltp`, `cvgrPdistC_lep`,
    `cvgr0Pnorm_le`, `cvgr0Pnorm_ltp`, `cvgr0Pnorm_lep`, `cvgr_norm_lt`,
    `cvgr_norm_le`, `cvgr_norm_gt`, `cvgr_norm_ge`, `cvgr_neq0`,
    `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_gt`, `real_cvgr_ge`, `cvgr_lt`,
    `cvgr_gt`, `cvgr_norm_lty`, `cvgr_norm_ley`, `cvgr_norm_gtNy`,
    `cvgr_norm_geNy`, `fcvgr2dist_ltP`, `cvgr2dist_ltP`, `cvgr2dist_lt`,
    `cvgNP`, `norm_cvg0P`, `cvgVP`, `is_cvgVE`, `cvgr_to_ge`, `cvgr_to_le`,
    `nbhs_EFin`, `nbhs_ereal_pinfty`, `nbhs_ereal_ninfty`, `fine_fcvg`,
    `fcvg_is_fine`, `fine_cvg`, `cvg_is_fine`, `cvg_EFin`, `neq0_fine_cvgP`,
    `cvgeNP`, `is_cvgeNE`, `cvge_to_ge`, `cvge_to_le`, `is_cvgeM`, `limeM`,
    `cvge_ge`, `cvge_le`, `lim_nnesum`, `ltr0_cvgV0`, `cvgrVNy`, `ler_cvg_to`,
    `gee_cvgy`, `lee_cvgNy`, `squeeze_fin`, and `lee_cvg_to`.
- in `normedtype.v`, added notations `^'+`, `^'-`, `+oo_R`, `-oo_R`
- in `sequences.v`,
  + lemma `invr_cvg0` and `invr_cvg_pinfty`
  + lemma `cvgPninfty_lt`, `cvgPpinfty_near`, `cvgPninfty_near`,
    `cvgPpinfty_lt_near` and `cvgPninfty_lt_near`
  + new lemma `nneseries_pinfty`.
  + lemmas `is_cvg_ereal_npos_natsum_cond`, `lee_npeseries`,
    `is_cvg_npeseries_cond`, `is_cvg_npeseries`, `npeseries_le0`,
    `is_cvg_ereal_npos_natsum`
  + lemma `nnseries_is_cvg`
- in `measure.v`:
  + definition `discrete_measurable_bool` with an instance of measurable type
  + lemmas `measurable_fun_if`, `measurable_fun_ifT`
  + lemma `measurable_fun_bool`
- in `lebesgue_measure.v`:
  + definition `ErealGenInftyO.R` and lemma `ErealGenInftyO.measurableE`
  + lemma `sub1set`
- in `lebesgue_integral.v`:
  + lemma `integral_cstNy`
  + lemma `ae_eq0`
  + lemma `integral_cst`
  + lemma `le_integral_comp_abse`
  + lemmas `integral_fune_lt_pinfty`, `integral_fune_fin_num`
  + lemmas `emeasurable_fun_fsum`, `ge0_integral_fsum`

### Changed

- in `constructive_ereal.v`:
  + lemmas `lee_paddl`, `lte_paddl`, `lee_paddr`, `lte_paddr`,
    `lte_spaddr`, `lee_pdaddl`, `lte_pdaddl`, `lee_pdaddr`,
    `lte_pdaddr`, `lte_spdaddr` generalized to `realDomainType`
  + generalize `lte_addl`, `lte_addr`, `gte_subl`, `gte_subr`,
    `lte_daddl`, `lte_daddr`, `gte_dsubl`, `gte_dsubr`
- in `topology.v`
  + definition `fct_restrictedUniformType` changed to use `weak_uniformType`
  + definition `family_cvg_topologicalType` changed to use `sup_uniformType`
  + lemmas `continuous_subspace0`, `continuous_subspace1`
- in `realfun.v`:
  + Instance for `GRing.opp` over real intervals
  + lemmas `itv_continuous_inj_le`, `itv_continuous_inj_ge`,
     `itv_continuous_inj_mono`, `segment_continuous_inj_le`,
     `segment_continuous_inj_ge`, `segment_can_le` ,
     `segment_can_ge`, `segment_can_mono`,
     `segment_continuous_surjective`, `segment_continuous_le_surjective`,
     `segment_continuous_ge_surjective`, `continuous_inj_image_segment`,
     `continuous_inj_image_segmentP`, `segment_continuous_can_sym`,
     `segment_continuous_le_can_sym`, `segment_continuous_ge_can_sym`,
     `segment_inc_surj_continuous`, `segment_dec_surj_continuous`,
     `segment_mono_surj_continuous`, `segment_can_le_continuous`,
     `segment_can_ge_continuous`, `segment_can_continuous`
     all have "{in I, continuous f}" replaced by "{within I, continuous f}"
- in `sequence.v`:
  + `nneseries_pinfty` generalized to `eseries_pinfty`
- in `measure.v`:
  + `covered_by_countable` generalized from `pointedType` to `choiceType`
- in `lebesgue_measure.v`:
  + definition `fimfunE` now uses fsbig
  + generalize and rename `eitv_c_infty` to `eitv_bnd_infty` and
    `eitv_infty_c` to `eitv_infty_bnd`
  + generalize `ErealGenOInfty.G`, `ErealGenCInfty.G`, `ErealGenInftyO.G`
- in `lebesgue_integral.v`:
  + implicits of `ae_eq_integral`
- moved from `mathcomp_extra.v` to `classical_sets.v`: `pred_oappE`, and
    `pred_oapp_set`.
- moved from `normedtype.v` to `mathcomp_extra.v`: `itvxx`, `itvxxP`,
    `subset_itv_oo_cc`, and `bound_side`.
- moved from `sequences.v` to `normedtype.v`: `ler_lim`.
- `sub_dominatedl` and `sub_dominatedr` generalized from
  `numFieldType` to `numDomainType`.
- `abse_fin_num` changed from an equivalence to an equality.
- `lee_opp2` and `lte_opp2` generalized from `realDomainType` to
  `numDomainType`.
- `cvgN`, `cvg_norm`, `is_cvg_norm` generalized from
  `normedModType`/`topologicalType` to
  `pseudoMetricNormedZmodType`/`Type`
- `cvgV`, `is_cvgV`, `cvgM`, `is_cvgM`, `is_cvgMr`, `is_cvgMl`,
  `is_cvgMrE`, `is_cvgMlE`, `limV`, `cvg_abse`, `is_cvg_abse`
  generalized from `TopologicalType` to `Type`
- `lim_norm` generalized from `normedModType`/`TopoligicalType` to
  `pseudoMetricNormedZmodType`/`Type`
- updated `cvg_ballP`, `cvg_ball2P`, `cvg_ball`, and `cvgi_ballP` to
  match a `f @ F` instead of just an `F`. The old lemmas are still
  available with prefix `f`.
- generalized `lee_lim` to any proper filter and moved from
  `sequences.v` to `normedtype.v`.
- generalized `ereal_nbhs_pinfty_ge` and `ereal_nbhs_ninfty_le`.
- renamed `nbhsN` to `nbhsNimage`  and `nbhsN` is now replaced by
  `nbhs (- x) = -%R @ x`
- fixed the statements of `nbhs_normP` which used to be an accidental
  alias of `nbhs_ballP` together with `nbhs_normE`,
  `nbhs_le_nbhs_norm`, `nbhs_norm_le_nbhs`, `near_nbhs_norm` and
  `nbhs_norm_ball` which were not about `nbhs_ball_ ball_norm` but
  should have been.
- `EFin_lim` generalized from `realType` to `realFieldType`

### Renamed

- file `theories/mathcomp_extra.v` moved to `classical/mathcomp_extra.v`
- file `theories/boolp.v` -> `classical/boolp.v`
- file `theories/classical_sets.v` -> `classical/classical_sets.v`
- file `theories/functions.v` -> `classical/functions.v`
- file `theories/cardinality.v` -> `classical/cardinality.v`
- file `theories/fsbigop.v` -> `classical/fsbigop.v`
- file `theories/set_interval.v` -> `theories/real_interval.v`
- in `mathcomp_extra.v`:
  + `homo_le_bigmax` -> `le_bigmax2`
- in `constructive_ereal.v`:
  + `lte_spdaddr` -> `lte_spdaddre`
  + `esum_ninftyP` -> `esum_eqNyP`
  + `esum_ninfty` -> `esum_eqNy`
  + `esum_pinftyP` -> `esum_eqyP`
  + `esum_pinfty` -> `esum_eqy`
  + `desum_pinftyP` -> `desum_eqyP`
  + `desum_pinfty` -> `desum_eqy`
  + `desum_ninftyP` -> `desum_eqNyP`
  + `desum_ninfty` -> `desum_eqNy`
  + `eq_pinftyP` -> `eqyP`
  + `ltey` -> `ltry`
  + `ltNye` -> `ltNyr`
- in `topology.v`:
  + renamed `continuous_subspaceT` to `continuous_in_subspaceT`
  + `pasting` -> `withinU_continuous`
  + `cvg_map_lim` -> `cvg_lim`
  + `cvgi_map_lim` -> `cvgi_lim`
  + `app_cvg_locally` -> `cvg_ball`
  + `prod_topo_apply_continuous` -> `proj_continuous`
- in `normedtype.v`,
  + `normmZ` -> `normrZ`
  + `norm_cvgi_map_lim` -> `norm_cvgi_lim`
  + `nbhs_image_ERFin` -> `nbhs_image_EFin`
- moved from `sequences.v` to `normedtype.v`:
  + `squeeze` -> `squeeze_cvgr`
- in `sequences.v`:
  + `nneseries0` -> `eseries0`
  + `nneseries_pred0` -> `eseries_pred0`
  + `eq_nneseries` -> `eq_eseries`
  + `nneseries_mkcond` -> `eseries_mkcond`
  + `seqDUE` -> `seqDU_seqD`
  + `elim_sup` -> `lim_esup`
  + `elim_inf` -> `lim_einf`
  + `elim_inf_shift` -> `lim_einf_shift`
  + `elim_sup_le_cvg` -> `lim_esup_le_cvg`
  + `elim_infN` -> `lim_einfN`
  + `elim_supN` -> `lim_esupN`
  + `elim_inf_sup` -> `lim_einf_sup`
  + `cvg_ninfty_elim_inf_sup` -> `cvgNy_lim_einf_sup`
  + `cvg_ninfty_einfs` -> `cvgNy_einfs`
  + `cvg_ninfty_esups` -> `cvgNy_esups`
  + `cvg_pinfty_einfs` -> `cvgy_einfs`
  + `cvg_pinfty_esups` -> `cvgy_esups`
  + `cvg_elim_inf_sup` -> `cvg_lim_einf_sup`
  + `is_cvg_elim_infE` -> `is_cvg_lim_einfE`
  + `is_cvg_elim_supE` -> `is_cvg_lim_esupE`
- in `measure.v`,
  + `caratheodory_lim_lee` -> `caratheodory_lime_le`
- in `lebesgue_measure.v`,
  + `measurable_fun_elim_sup` -> `measurable_fun_lim_esup`
- moved from `lebesgue_measure.v` to `real_interval.v`:
  + `itv_cpinfty_pinfty` -> `itv_cyy`
  + `itv_opinfty_pinfty` -> `itv_oyy`
  + `itv_cninfty_pinfty` -> `itv_cNyy`
  + `itv_oninfty_pinfty` -> `itv_oNyy`
- in `lebesgue_integral.v`:
  + `integral_cst_pinfty` -> `integral_csty`
  + `sintegral_cst` -> `sintegral_EFin_cst`
  + `integral_cst` -> `integral_cstr`

### Generalized

- in `constructive_ereal.v`,
  + `daddooe` -> `daddye`
  + `daddeoo` -> `daddey`
  + `ltey`, `ltNye`
- moved from `normedtype.v` to `mathcomp_extra.v`:
  + `ler0_addgt0P` -> `ler_gtP`
- in `normedtype.v`,
  + `cvg_gt_ge` -> `cvgr_ge`
  + `cvg_lt_le` -> `cvgr_le`
  + `cvg_dist0` -> `norm_cvg0`
  + `ereal_cvgN` -> `cvgeN`
  + `ereal_is_cvgN` -> `is_cvgeN`
  + `ereal_cvgrM` -> `cvgeMl`
  + `ereal_is_cvgrM` -> `is_cvgeMl`
  + `ereal_cvgMr` -> `cvgeMr`
  + `ereal_is_cvgMr` -> `is_cvgeMr`
  + `ereal_limrM` -> `limeMl`
  + `ereal_limMr` -> `limeMr`
  + `ereal_limN` -> `limeN`
  + `linear_continuous0` -> `continuous_linear_bounded`
  + `linear_bounded0` -> `bounded_linear_continuous`
- moved from `derive.v` to `normedtype.v`:
  + `le0r_cvg_map` -> `limr_ge`
  + `ler0_cvg_map` -> `limr_le`
- moved from `sequences.v` to `normedtype.v`:
  + `ereal_cvgM` -> `cvgeM`
  + `cvgPpinfty` -> `cvgryPge`
  + `cvgPninfty` -> `cvgrNyPle`
  + `ger_cvg_pinfty` -> `ger_cvgy`
  + `ler_cvg_ninfty` -> `ler_cvgNy`
  + `cvgPpinfty_lt` -> `cvgryPgt`
  + `cvgPninfty_lt` -> `cvgrNyPlt`
  + `cvgPpinfty_near` -> `cvgryPgey`
  + `cvgPninfty_near` -> `cvgrNyPleNy`
  + `cvgPpinfty_lt_near` -> `cvgryPgty`
  + `cvgPninfty_lt_near` -> `cvgrNyPltNy`
  + `invr_cvg0` -> `gtr0_cvgV0`
  + `invr_cvg_pinfty` -> `cvgrVy`
  + `nat_dvg_real` -> `cvgrnyP`
  + `ereal_cvg_abs0` -> `cvg_abse0P`
  + `ereal_lim_ge` -> `lime_ge`
  + `ereal_lim_le` -> `lime_le`
  + `dvg_ereal_cvg` -> `cvgeryP`
  + `ereal_cvg_real` -> `fine_cvgP`
  + `ereal_squeeze` -> `squeeze_cvge`
  + `ereal_cvgD` -> `cvgeD`
  + `ereal_cvgB` -> `cvgeB`
  + `ereal_is_cvgD` -> `is_cvgeD`
  + `ereal_cvg_sub0` -> `cvge_sub0`
  + `ereal_limD` -> `limeD`
  + `ereal_lim_sum` -> `cvg_nnesum`
- moved from `sequences.v` to `topology.v`:
  + `nat_cvgPpinfty` -> `cvgnyPge`
- in `topology.v`
  + `prod_topo_apply` -> `proj`
- in `lebesgue_integral.v`:
  + `integral_sum` -> `integral_nneseries`

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr`, renamed `lte_spaddre`
- in `topology.v`, deprecated
  + `cvg_ballPpos` (use a combination of `cvg_ballP` and `posnumP`),
  + `cvg_dist` (use `cvgr_dist_lt` or a variation instead)
- in `normedtype.v`, deprecated
  + `cvg_distP` (use `cvgrPdist_lt` or a variation instead),
  + `cvg_dist` (use `cvg_dist_lt` or a variation instead),
  + `cvg_distW` (use `cvgrPdist_le` or a variation instead),
  + `cvg_bounded_real` (use `cvgr_norm_lty` or a variation instead),
  + `continuous_cvg_dist` (simply use the fact that `(x --> l) -> (x = l)`),
  + `cvg_dist2P` (use `cvgr2dist_ltP` or a variant instead),
  + `cvg_dist2` (use `cvgr2dist_lt` or a variant instead),
- in `derive.v`, deprecated
  + `ler_cvg_map` (subsumed by `ler_lim`),
- in `sequences.v`, deprecated
  + `cvgNpinfty` (use `cvgNry` instead),
  + `cvgNninfty` (use `cvgNrNy` instead),
  + `ereal_cvg_ge0` (use `cvge_ge` instead),
  + `ereal_cvgPpinfty` (use `cvgeyPge` or a variant instead),
  + `ereal_cvgPninfty` (use `cvgeNyPle` or a variant instead),
  + `ereal_cvgD_pinfty_fin` (use `cvgeD` instead),
  + `ereal_cvgD_ninfty_fin` (use `cvgeD` instead),
  + `ereal_cvgD_pinfty_pinfty` (use `cvgeD` instead),
  + `ereal_cvgD_ninfty_ninfty` (use `cvgeD` instead),
  + `ereal_cvgM_gt0_pinfty` (use `cvgeM` instead),
  + `ereal_cvgM_lt0_pinfty` (use `cvgeM` instead),
  + `ereal_cvgM_gt0_ninfty` (use `cvgeM` instead),
  + `ereal_cvgM_lt0_ninfty` (use `cvgeM` instead),

### Removed

- in `classical_sets.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (moved to `mathcomp_extra.v`)
- in `fsbigop.v`:
  + notation `\sum_(_ \in _) _` (moved to `ereal.v`)
  + lemma `lee_fsum_nneg_subset`, `lee_fsum`, `ge0_mule_fsumr`,
    `ge0_mule_fsuml`, `fsume_ge0`, `fsume_le0`, `fsume_gt0`,
    `fsume_lt0`, `pfsume_eq0` (moved to `ereal.v`)
  + lemma `pair_fsum` (subsumed by `pair_fsbig`)
  + lemma `exchange_fsum` (subsumed by `exchange_fsbig`)
- in `reals.v`:
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (moved to `classical/set_interval.v`)
- in `set_interval.v`:
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`,
    `disjoint_itv`, `conv`, `factor`, `ndconv` (moved to `classical/set_interval.v`)
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itv_cc`,
    `set_itvco`, `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`,
    `set_itv_infty_infty`, `set_itv_o_infty`, `set_itv_c_infty`, `set_itv_infty_o`,
    `set_itv_infty_c`, `set_itv_pinfty_bnd`, `set_itv_bnd_ninfty`, `setUitv1`,
    `setU1itv`, `set_itvI`, `neitvE`, `neitvP`, `setitv0`, `has_lbound_itv`,
    `has_ubound_itv`, `hasNlbound`, `hasNubound`, `opp_itv_bnd_infty`,
    `opp_itv_infty_bnd`, `opp_itv_bnd_bnd`, `opp_itvoo`,
    `setCitvl`, `setCitvr`, `set_itv_splitI`, `setCitv`, `set_itv_splitD`,
    `mem_1B_itvcc`, `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`,
    `conv1`, `conv_sym`, `conv_flat`, `leW_conv`, `leW_factor`,
    `factor_flat`, `factorl`, `ndconvE`, `factorr`, `factorK`,
    `convK`, `conv_inj`, `factor_inj`, `conv_bij`, `factor_bij`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`, `conv_itv_bij`,
    `factor_itv_bij`, `mem_conv_itv`, `mem_conv_itvcc`, `range_conv`,
    `range_factor`, `mem_factor_itv`,
    `set_itv_ge`, `trivIset_set_itv_nth`, `disjoint_itvxx`, `lt_disjoint`,
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (moved to `classical/set_interval.v`)
- in `topology.v`
  + lemmas `prod_topo_applyE`

## [0.5.4] - 2022-09-07

### Added

- in `mathcomp_extra.v`:
  + defintion `onem` and notation ``` `1- ```
  + lemmas `onem0`, `onem1`, `onemK`, `onem_gt0`, `onem_ge0`, `onem_le1`, `onem_lt1`,
    `onemX_ge0`, `onemX_lt1`, `onemD`, `onemMr`, `onemM`
  + lemmas `natr1`, `nat1r`
- in `classical_sets.v`:
  + lemmas `subset_fst_set`, `subset_snd_set`, `fst_set_fst`, `snd_set_snd`,
    `fset_setM`, `snd_setM`, `fst_setMR`
  + lemmas `xsection_snd_set`, `ysection_fst_set`
- in `constructive_ereal.v`:
  + lemmas `ltNye_eq`, `sube_lt0`, `subre_lt0`, `suber_lt0`, `sube_ge0`
  + lemmas `dsubre_gt0`, `dsuber_gt0`, `dsube_gt0`, `dsube_le0`
- in `signed.v`:
  + lemmas `onem_PosNum`, `onemX_NngNum`
- in `fsbigop.v`:
  + lemmas `lee_fsum_nneg_subset`, `lee_fsum`
- in `topology.v`:
  + lemma `near_inftyS`
  + lemma `continuous_closedP`, `closedU`, `pasting`
  + lemma `continuous_inP`
  + lemmas `open_setIS`, `open_setSI`, `closed_setIS`, `closed_setSI`
- in `normedtype.v`:
  + definitions `contraction` and `is_contraction`
  + lemma `contraction_fixpoint_unique`
- in `sequences.v`:
  + lemmas `contraction_dist`, `contraction_cvg`,
    `contraction_cvg_fixed`, `banach_fixed_point`,
    `contraction_unique`
- in `derive.v`:
  + lemma `diff_derivable`
- in `measure.v`:
  + lemma `measurable_funTS`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_fine`
  + lemma `open_measurable_subspace`
  + lemma ``subspace_continuous_measurable_fun``
  + corollary `open_continuous_measurable_fun`
  + Hint about `measurable_fun_normr`
- in `lebesgue_integral.v`:
  + lemma `measurable_fun_indic`
  + lemma `ge0_integral_mscale`
  + lemma `integral_pushforward`

### Changed

- in `esum.v`:
  + definition `esum`
- moved from `lebesgue_integral.v` to `classical_sets.v`:
  + `mem_set_pair1` -> `mem_xsection`
  + `mem_set_pair2` -> `mem_ysection`
- in `derive.v`:
  + generalized `is_diff_scalel`
- in `measure.v`:
  + generalize `measurable_uncurry`
- in `lebesgue_measure.v`:
  + `pushforward` requires a proof that its argument is measurable
- in `lebesgue_integral.v`:
  + change implicits of `integralM_indic`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pinfty_eq` -> `ltey_eq`
  + `le0R` -> `fine_ge0`
  + `lt0R` -> `fine_gt0`
- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `esum.v`:
  + `esum0` -> `esum1`
- in `sequences.v`:
  + `nneseries_lim_ge0` -> `nneseries_ge0`
- in `measure.v`:
  + `ring_fsets` -> `ring_finite_set`
  + `discrete_measurable` -> `discrete_measurable_nat`
  + `cvg_mu_inc` -> `nondecreasing_cvg_mu`
- in `lebesgue_integral.v`:
  + `muleindic_ge0` -> `nnfun_muleindic_ge0`
  + `mulem_ge0` -> `mulemu_ge0`
  + `nnfun_mulem_ge0` -> `nnsfun_mulemu_ge0`

### Removed

- in `esum.v`:
  + lemma `fsetsP`, `sum_fset_set`

## [0.5.3] - 2022-08-10

### Added

- in `mathcomp_extra.v`:
  + lemma `big_const_idem`
  + lemma `big_id_idem`
  + lemma `big_rem_AC`
  + lemma `bigD1_AC`
  + lemma `big_mkcond_idem`
  + lemma `big_split_idem`
  + lemma `big_id_idem_AC`
  + lemma `bigID_idem`
  + lemmas `bigmax_le` and `bigmax_lt`
  + lemma `bigmin_idr`
  + lemma `bigmax_idr`
- in file `boolp.v`:
  + lemmas `iter_compl`, `iter_compr`, `iter0`
- in file `functions.v`:
  + lemmas `oinv_iter`, `some_iter_inv`, `inv_iter`,
  + Instances for functions interfaces for `iter` (partial inverse up to
      bijective function)
- in `classical_sets.v`:
  + lemma `preimage10P`
  + lemma `setT_unit`
  + lemma `subset_refl`
- in `ereal.v`:
  + notations `_ < _ :> _` and `_ <= _ :> _`
  + lemmas `lee01`, `lte01`, `lee0N1`, `lte0N1`
  + lemmas `lee_pmul2l`, `lee_pmul2r`, `lte_pmul`, `lee_wpmul2l`
  + lemmas `lee_lt_add`, `lee_lt_dadd`, `lee_paddl`, `lee_pdaddl`,
    `lte_paddl`, `lte_pdaddl`, `lee_paddr`, `lee_pdaddr`,
    `lte_paddr`, `lte_pdaddr`
  + lemmas `muleCA`, `muleAC`, `muleACA`
- in `reals.v`:
  + lemmas `Rfloor_lt_int`, `floor_lt_int`, `floor_ge_int`
  + lemmas `ceil_ge_int`, `ceil_lt_int`
- in `lebesgue_integral.v`:
  + lemma `ge0_emeasurable_fun_sum`
  + lemma `integrableMr`

### Changed

- in `ereal.v`:
  + generalize `lee_pmul`
  + simplify `lte_le_add`, `lte_le_dadd`, `lte_le_sub`, `lte_le_dsub`
- in `measure.v`:
  + generalize `pushforward`
- in `lebesgue_integral.v`
  + change `Arguments` of `eq_integrable`
  + fix pretty-printing of `{mfun _ >-> _}`, `{sfun _ >-> _}`, `{nnfun _ >-> _}`
  + minor generalization of `eq_measure_integral`
- from `topology.v` to `mathcomp_extra.v`:
  + generalize `ltr_bigminr` to `porderType` and rename to `bigmin_lt`
  + generalize `bigminr_ler` to `orderType` and rename to `bigmin_le`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v`
  and generalized to `orderType`:
  + lemma `bigminr_ler_cond`, renamed to `bigmin_le_cond`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v`:
  + lemma `bigminr_maxr`
- moved from from module `Bigminr` in `normedtype.v`
  + to `mathcomp_extra.v` and generalized to `orderType`
    * `bigminr_mkcond` -> `bigmin_mkcond`
    * `bigminr_split` -> `bigmin_split`
    * `bigminr_idl` -> `bigmin_idl`
    * `bigminrID` -> `bigminID`
    * `bigminrD1` -> `bigminD1`
    * `bigminr_inf` -> `bigmin_inf`
    * `bigminr_gerP` -> `bigmin_geP`
    * `bigminr_gtrP` -> ``bigmin_gtP``
    * `bigminr_eq_arg` -> `bigmin_eq_arg`
    * `eq_bigminr` -> `eq_bigmin`
  + to `topology.v` and generalized to `orderType`
    * `bigminr_lerP` -> `bigmin_leP`
    * `bigminr_ltrP` -> `bigmin_ltP`
- moved from `topology.v` to `mathcomp_extra.v`:
  + `bigmax_lerP` -> `bigmax_leP`
  + `bigmax_ltrP` -> `bigmax_ltP`
  + `ler_bigmax_cond` -> `le_bigmax_cond`
  + `ler_bigmax` -> `le_bigmax`
  + `le_bigmax` -> `homo_le_bigmax`

### Renamed

- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `classical_sets.v`:
  + `set_bool` -> `setT_bool`
- in `topology.v`:
  + `bigmax_gerP` -> `bigmax_geP`
  + `bigmax_gtrP` -> `bigmax_gtP`
- in `lebesgue_integral.v`:
  + `emeasurable_funeM` -> `measurable_funeM`

### Removed

- in `topology.v`:
  + `bigmax_seq1`, `bigmax_pred1_eq`, `bigmax_pred1`
- in `normedtype.v` (module `Bigminr`)
  + `bigminr_ler_cond`, `bigminr_ler`.
  + `bigminr_seq1`, `bigminr_pred1_eq`, `bigminr_pred1`

### Misc

- file `ereal.v` split in two files `constructive_ereal.v` and
  `ereal.v` (the latter exports the former, so the "Require Import
  ereal" can just be kept unchanged)

## [0.5.2] - 2022-07-08

### Added

- in file `classical_sets.v`
  + lemma `set_bool`
  + lemma `supremum_out`
  + definition `isLub`
  + lemma `supremum1`
  + lemma `trivIset_set0`
  + lemmas `trivIset_image`, `trivIset_comp`
  + notation `trivIsets`
- in file `topology.v`:
  + definition `near_covering`
  + lemma `compact_near_coveringP`
  + lemma `continuous_localP`, `equicontinuous_subset_id`
  + lemmas `precompact_pointwise_precompact`, `precompact_equicontinuous`,
    `Ascoli`
  + definition `frechet_filter`, instances `frechet_properfilter`, and `frechet_properfilter_nat`
  + definition `principal_filter` `discrete_space`
  + lemma `principal_filterP`, `principal_filter_proper`,
      `principal_filter_ultra`
  + canonical `bool_discrete_filter`
  + lemma `compactU`
  + lemma `discrete_sing`, `discrete_nbhs`, `discrete_open`, `discrete_set1`,
      `discrete_closed`, `discrete_cvg`, `discrete_hausdorff`
  + canonical `bool_discrete_topology`
  + definition `discrete_topological_mixin`
  + lemma `discrete_bool`, `bool_compact`
- in `Rstruct.v`:
  + lemmas `Rsupremums_neq0`, `Rsup_isLub`, `Rsup_ub`
- in `reals.v`:
  + lemma `floor_natz`
  + lemma `opp_set_eq0`, `ubound0`, `lboundT`
- in file `lebesgue_integral.v`:
  + lemma `integrable0`
  + mixins `isAdditiveMeasure`, `isMeasure0`, `isMeasure`, `isOuterMeasure`
  + structures `AdditiveMeasure`, `Measure`, `OuterMeasure`
  + notations `additive_measure`, `measure`, `outer_measure`
  + definition `mrestr`
  + lemmas `integral_measure_sum_nnsfun`, `integral_measure_add_nnsfun`
  + lemmas `ge0_integral_measure_sum`, `integral_measure_add`, `integral_measure_series_nnsfun`,
    `ge0_integral_measure_series`
  + lemmas `integrable_neg_fin_num`, `integrable_pos_fin_num`
  + lemma `integral_measure_series`
  + lemmas `counting_dirac`, `summable_integral_dirac`, `integral_count`
  + lemmas `integrable_abse`, `integrable_summable`, `integral_bigcup`
- in `measure.v`:
  + lemmas `additive_measure_snum_subproof`, `measure_snum_subproof`
  + canonicals `additive_measure_snum`, `measure_snum`
  + definition `mscale`
  + definition `restr`
  + definition `counting`, canonical `measure_counting`
  + definition `discrete_measurable`, instantiated as a `measurableType`
  + lemma `sigma_finite_counting`
  + lemma `msum_mzero`
- in `lebesgue_measure.v`:
  + lemma `diracE`
  + notation `_.-ocitv`
  + definition `ocitv_display`
- in file `cardinality.v`:
  + lemmas `trivIset_sum_card`, `fset_set_sub`, `fset_set_set0`
- in file `sequences.v`:
  + lemmas `nat_dvg_real`, `nat_cvgPpinfty`, `nat_nondecreasing_is_cvg`
  + definition `nseries`, lemmas `le_nseries`, `cvg_nseries_near`, `dvg_nseries`
- in file `ereal.v`:
  + lemma `fin_num_abs`
- in file `esum.v`:
  + definition `summable`
  + lemmas `summable_pinfty`, `summableE`, `summableD`, `summableN`, `summableB`,
    `summable_funepos`, `summable_funeneg`
  + lemmas `summable_fine_sum`, `summable_cvg`, `summable_nneseries_lim`,
    `summable_nnseries`, `summable_nneseries_esum`, `esumB`
  + lemma `fsbig_esum`
- in `trigo.v`:
  + lemmas `cos1_gt0`, `pi_ge2`
  + lemmas `pihalf_ge1`, `pihalf_lt2`
- in `measure.v`:
  + inductive `measure_display`
  + notation `_.-sigma`, `_.-sigma.-measurable`,
             `_.-ring`, `_.-ring.-measurable`,
             `_.-cara`, `_.-cara.-measurable`,
             `_.-caratheodory`,
             `_.-prod`. `_.-prod.-measurable`
  + notation `_.-measurable`
  + lemma `measure_semi_additive_ord`, `measure_semi_additive_ord_I`
  + lemma `decomp_finite_set`
- in `functions.v`:
  + lemma `patch_pred`, `trivIset_restr`
- `has_sup1`, `has_inf1` moved from `reals.v` to `classical_sets.v`

### Changed

- in `topology.v`:
  + generalize `cluster_cvgE`, `fam_cvgE`, `ptws_cvg_compact_family`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index
- in `Rstruct.v`:
  + statement of lemma `completeness'`, renamed to `Rcondcomplete`
  + statement of lemma `real_sup_adherent`
- in `ereal.v`:
  + statements of lemmas `ub_ereal_sup_adherent`, `lb_ereal_inf_adherent`
- in `reals.v`:
  + definition `sup`
  + statements of lemmas `sup_adherent`, `inf_adherent`
- in `sequences.v`:
  + generalize `eq_nneseries`, `nneseries0`
- in `mathcomp_extra.v`:
  + generalize `card_fset_sum1`
- in `lebesgue_integral.v`:
  + change the notation `\int_`
  + `product_measure1` takes a proof that the second measure is sigma-finite
  + `product_measure2` takes a proof that the first measure is sigma-finite
  + definitions `integral` and `integrable` now take a function instead of a measure
  + remove one space in notation `\d_`
  + generalize `nondecreasing_series`
  + constant `measurableType` now take an addititional parameter of type `measure_display`
- in `measure.v`:
  + `measure0` is now a lemma
  + statement of lemmas `content_fin_bigcup`, `measure_fin_bigcup`, `ring_fsets`,
    `decomp_triv`, `cover_decomp`, `decomp_set0`, `decompN0`, `Rmu_fin_bigcup`
  + definitions `decomp`, `measure`
  + several constants now take a parameter of type `measure_display`
- in `trigo.v`:
  + lemma `cos_exists`
- in `set_interval.v`:
  + generalize to numDomainType:
    * `mem_1B_itvcc`, `conv`, `conv_id`, `convEl`, `convEr`,
    `conv10`, `conv0`, `conv1`, `conv_sym`, `conv_flat`, `leW_conv`,
    `factor`, `leW_factor`, `factor_flat`, `factorl`, `ndconv`,
    `ndconvE`
  + generalize to numFieldType
    * `factorr`, `factorK`, `convK`, `conv_inj`, `factor_inj`,
    `conv_bij`, `factor_bij`, `le_conv`, `le_factor`, `lt_conv`,
    `lt_factor`, `conv_itv_bij`, `factor_itv_bij`, `mem_conv_itv`,
    `mem_conv_itvcc`, `range_conv`, `range_factor`
  + generalize to realFieldType:
    * `mem_factor_itv`
- in `fsbig.v`:
  + generalize `exchange_fsum`
- lemma `preimage_cst` generalized and moved from `lebesgue_integral.v`
  to `functions.v`
- lemma `fset_set_image` moved from `measure.v` to `cardinality.v`
- in `reals.v`:
  + type generalization of `has_supPn`

### Renamed

- in `lebesgue_integral.v`:
  + `integralK` -> `integralrM`
- in `trigo.v`:
  + `cos_pihalf_uniq` -> `cos_02_uniq`
- in `measure.v`:
  + `sigma_algebraD` -> `sigma_algebraCD`
  + `g_measurable` -> `salgebraType`
  + `g_measurable_eqType` -> `salgebraType_eqType`
  + `g_measurable_choiceType` -> `salgebraType_choiceType`
  + `g_measurable_ptType` -> `salgebraType_ptType`
- in `lebesgue_measure.v`:
  + `itvs` -> `ocitv_type`
  + `measurable_fun_sum` -> `emeasurable_fun_sum`
- in `classical_sets.v`:
  + `trivIset_restr` -> `trivIset_widen`
  + `supremums_set1` -> `supremums1`
  + `infimums_set1` -> `infimums1`

### Removed

- in `Rstruct.v`:
  + definition `real_sup`
  + lemma `real_sup_is_lub`, `real_sup_ub`, `real_sup_out`
- in `reals.v`:
  + field `sup` from `mixin_of` in module `Real`
- in `measure.v`:
  + notations `[additive_measure _ -> _]`, `[measure _ -> _]`, `[outer_measure _ -> _ ]`,
  + lemma `measure_is_additive_measure`
  + definitions `caratheodory_measure_mixin`, `caratheodory_measure`
  + coercions `measure_to_nadditive_measure`, `measure_additive_measure`
  + canonicals `measure_additive_measure`, `set_ring_measure`,
    `outer_measure_of_measure`, `Hahn_ext_measure`
  + lemma `Rmu0`
  + lemma `measure_restrE`
- in `measure.v`:
  + definition `g_measurableType`
  + notation `mu.-measurable`

## [0.5.1] - 2022-06-04

### Added

- in `mathcomp_extra.v`:
  + lemma `card_fset_sum1`
- in `classical_sets.v`:
  + lemma `preimage_setT`
  + lemma `bigsetU_bigcup`
  + lemmas `setI_II` and `setU_II`
- in `topology.v`:
  + definition `powerset_filter_from`
  + globals `powerset_filter_from_filter`
  + lemmas `near_small_set`, `small_set_sub`
  + lemmas `withinET`, `closureEcvg`, `entourage_sym`, `fam_nbhs`
  + generalize `cluster_cvgE`, `ptws_cvg_compact_family`
  + lemma `near_compact_covering`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index
  + lemmas `ptws_cvg_entourage`, `equicontinuous_closure`, `ptws_compact_cvg`
    `ptws_compact_closed`, `ascoli_forward`, `compact_equicontinuous`
- in `normedtype.v`:
  + definition `bigcup_ointsub`
  + lemmas `bigcup_ointsub0`, `open_bigcup_ointsub`, `is_interval_bigcup_ointsub`,
    `bigcup_ointsub_sub`, `open_bigcup_rat`
  + lemmas `mulrl_continuous` and `mulrr_continuous`.
- in `ereal.v`:
  + definition `expe` with notation `^+`
  + definition `enatmul` with notation `*+` (scope `%E`)
  + definition `ednatmul` with notation `*+` (scope `%dE`)
  + lemmas `fineM`, `enatmul_pinfty`, `enatmul_ninfty`, `EFin_natmul`, `mule2n`, `expe2`,
    `mule_natl`
  + lemmas `ednatmul_pinfty`, `ednatmul_ninfty`, `EFin_dnatmul`, `dmule2n`, `ednatmulE`,
    `dmule_natl`
  + lemmas `sum_fin_num`, `sum_fin_numP`
  + lemmas `oppeB`, `doppeB`, `fineB`, `dfineB`
  + lemma `abse1`
  + lemma `ltninfty_adde_def`
- in `esum.v`:
  + lemma `esum_set1`
  + lemma `nnseries_interchange`
- in `cardinality.v`:
  + lemma `fset_set_image`, `card_fset_set`, `geq_card_fset_set`,
    `leq_card_fset_set`, `infinite_set_fset`, `infinite_set_fsetP` and
    `fcard_eq`.
- in `sequences.v`:
  + lemmas `nneseriesrM`, `ereal_series_cond`, `ereal_series`, `nneseries_split`
  + lemmas `lee_nneseries`
- in `numfun.v`:
  + lemma `restrict_lee`
- in `measure.v`:
  + definition `pushforward` and canonical `pushforward_measure`
  + definition `dirac` with notation `\d_` and canonical `dirac_measure`
  + lemmas `finite_card_dirac`, `infinite_card_dirac`
  + lemma `eq_measure`
  + definition `msum` and canonical `measure_sum'`
  + definition `mzero` and canonical `measure_zero'`
  + definition `measure_add` and lemma `measure_addE`
  + definition `mseries` and canonical `measure_series'`
- in `set_interval.v`:
  + lemma `opp_itv_infty_bnd`
- in `lebesgue_integral.v`:
  + lemmas `integral_set0`, `ge0_integral_bigsetU`, `ge0_integral_bigcup`
- in `lebesgue_measure.v`:
  + lemmas `is_interval_measurable`, `open_measurable`, `continuous_measurable_fun`
  + lemma `emeasurable_funN`
  + lemmas `itv_bnd_open_bigcup`, `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`,
    `itv_open_bnd_bigcup`
  + lemma `lebesgue_measure_set1`
  + lemma `lebesgue_measure_itv`
  + lemma `lebesgue_measure_rat`
- in `lebesgue_integral.v`:
  + lemmas `integralM_indic`, `integralM_indic_nnsfun`, `integral_dirac`
  + lemma `integral_measure_zero`
  + lemma `eq_measure_integral`

### Changed

- in `mathcomp_extra.v`:
  + generalize `card_fset_sum1`
- in `classical_sets.v`:
  + lemma `some_bigcup` generalized and renamed to `image_bigcup`
- in `esumv`:
  + remove one hypothesis in lemmas `reindex_esum`, `esum_image`
- moved from `lebesgue_integral.v` to `lebesgue_measure.v` and generalized
  + hint `measurable_set1`/`emeasurable_set1`
- in `sequences.v`:
  + generalize `eq_nneseries`, `nneseries0`
- in `set_interval.v`:
  + generalize `opp_itvoo` to `opp_itv_bnd_bnd`
- in `lebesgue_integral.v`:
  + change the notation `\int_`

### Renamed

- in `ereal.v`:
  + `num_abs_le` -> `num_abse_le`
  + `num_abs_lt` -> `num_abse_lt`
  + `addooe` -> `addye`
  + `addeoo` -> `addey`
  + `mule_ninfty_pinfty` -> `mulNyy`
  + `mule_pinfty_ninfty` -> `mulyNy`
  + `mule_pinfty_pinfty` -> `mulyy`
  + `mule_ninfty_ninfty` -> `mulNyNy`
  + `lte_0_pinfty` -> `lt0y`
  + `lte_ninfty_0` -> `ltNy0`
  + `lee_0_pinfty` -> `le0y`
  + `lee_ninfty_0` -> `leNy0`
  + `lte_pinfty` -> `ltey`
  + `lte_ninfty` -> `ltNye`
  + `lee_pinfty` -> `leey`
  + `lee_ninfty` -> `leNye`
  + `mulrpinfty_real` -> `real_mulry`
  + `mulpinftyr_real` -> `real_mulyr`
  + `mulrninfty_real` -> `real_mulrNy`
  + `mulninftyr_real` -> `real_mulNyr`
  + `mulrpinfty` -> `mulry`
  + `mulpinftyr` -> `mulyr`
  + `mulrninfty` -> `mulrNy`
  + `mulninftyr` -> `mulNyr`
  + `gt0_mulpinfty` -> `gt0_mulye`
  + `lt0_mulpinfty` -> `lt0_mulye`
  + `gt0_mulninfty` -> `gt0_mulNye`
  + `lt0_mulninfty` -> `lt0_mulNye`
  + `maxe_pinftyl` -> `maxye`
  + `maxe_pinftyr` -> `maxey`
  + `maxe_ninftyl` -> `maxNye`
  + `maxe_ninftyr` -> `maxeNy`
  + `mine_ninftyl` -> `minNye`
  + `mine_ninftyr` -> `mineNy`
  + `mine_pinftyl` -> `minye`
  + `mine_pinftyr` -> `miney`
  + `mulrinfty_real` -> `real_mulr_infty`
  + `mulrinfty` -> `mulr_infty`
- in `realfun.v`:
  + `exp_continuous` -> `exprn_continuous`
- in `sequences.v`:
  + `ereal_pseriesD` -> `nneseriesD`
  + `ereal_pseries0` -> `nneseries0`
  + `ereal_pseries_pred0` -> `nneseries_pred0`
  + `eq_ereal_pseries` -> `eq_nneseries`
  + `ereal_pseries_sum_nat` -> `nneseries_sum_nat`
  + `ereal_pseries_sum` -> `nneseries_sum`
  + `ereal_pseries_mkcond` -> `nneseries_mkcond`
  + `ereal_nneg_series_lim_ge` -> `nneseries_lim_ge`
  + `is_cvg_ereal_nneg_series_cond` -> `is_cvg_nneseries_cond`
  + `is_cvg_ereal_nneg_series` -> `is_cvg_nneseries`
  + `ereal_nneg_series_lim_ge0` -> `nneseries_lim_ge0`
  + `adde_def_nneg_series` -> `adde_def_nneseries`
- in `esum.v`:
  + `ereal_pseries_esum` -> `nneseries_esum`
- in `numfun.v`:
  + `funenng` -> `funepos`
  + `funennp` -> `funeneg`
  + `funenng_ge0` -> `funepos_ge0`
  + `funennp_ge0` -> `funeneg_ge0`
  + `funenngN` -> `funeposN`
  + `funennpN` -> `funenegN`
  + `funenng_restrict` -> `funepos_restrict`
  + `funennp_restrict` -> `funeneg_restrict`
  + `ge0_funenngE` -> `ge0_funeposE`
  + `ge0_funennpE` -> `ge0_funenegE`
  + `le0_funenngE` -> `le0_funeposE`
  + `le0_funennpE` -> `le0_funenegE`
  + `gt0_funenngM` -> `gt0_funeposM`
  + `gt0_funennpM` -> `gt0_funenegM`
  + `lt0_funenngM` -> `lt0_funeposM`
  + `lt0_funennpM` -> `lt0_funenegM`
  + `funenngnnp` -> `funeposneg`
  + `add_def_funennpg` -> `add_def_funeposneg`
  + `funeD_Dnng` -> `funeD_Dpos`
  + `funeD_nngD` -> `funeD_posD`
- in `lebesgue_measure.v`:
  + `emeasurable_fun_funenng` -> `emeasurable_fun_funepos`
  + `emeasurable_fun_funennp` -> `emeasurable_fun_funeneg`
- in `lebesgue_integral.v`:
  + `integrable_funenng` -> `integrable_funepos`
  + `integrable_funennp` -> `integrable_funeneg`
  + `integral_funennp_lt_pinfty` -> `integral_funeneg_lt_pinfty`
  + `integral_funenng_lt_pinfty` -> `integral_funepos_lt_pinfty`
  + `ae_eq_funenng_funennp` -> `ae_eq_funeposneg`

### Removed

- in `mathcomp_extra.v`:
  + lemmas `natr_absz`, `ge_pinfty`, `le_ninfty`, `gt_pinfty`,
    `lt_ninfty`
- in `classical_sets.v`:
  + notation `[set of _]`
- in `topology.v`:
  + lemmas `inj_can_sym_in_on`, `inj_can_sym_on`, `inj_can_sym_in`

## [0.5.0] - 2022-03-23

### Added

- in `signed.v`:
  + notations `%:nngnum` and `%:posnum`
- in `ereal.v`:
  + notations `{posnum \bar R}` and `{nonneg \bar R}`
  + notations `%:pos` and `%:nng` in `ereal_dual_scope` and `ereal_scope`
  + variants `posnume_spec` and `nonnege_spec`
  + definitions `posnume`, `nonnege`, `abse_reality_subdef`,
    `ereal_sup_reality_subdef`, `ereal_inf_reality_subdef`
  + lemmas `ereal_comparable`, `pinfty_snum_subproof`, `ninfty_snum_subproof`,
    `EFin_snum_subproof`, `fine_snum_subproof`, `oppe_snum_subproof`,
    `adde_snum_subproof`, `dadde_snum_subproof`, `mule_snum_subproof`,
    `abse_reality_subdef`, `abse_snum_subproof`, `ereal_sup_snum_subproof`,
    `ereal_inf_snum_subproof`, `num_abse_eq0`, `num_lee_maxr`, `num_lee_maxl`,
    `num_lee_minr`, `num_lee_minl`, `num_lte_maxr`, `num_lte_maxl`,
    `num_lte_minr`, `num_lte_minl`, `num_abs_le`, `num_abs_lt`,
    `posnumeP`, `nonnegeP`
  + signed instances `pinfty_snum`, `ninfty_snum`, `EFin_snum`, `fine_snum`,
    `oppe_snum`, `adde_snum`, `dadde_snum`, `mule_snum`, `abse_snum`,
    `ereal_sup_snum`, `ereal_inf_snum`

### Changed

- in `functions.v`:
  + `addrfunE` renamed to `addrfctE` and generalized to `Type`, `zmodType`
  + `opprfunE` renamed to `opprfctE` and generalized to `Type`, `zmodType`
- moved from `functions.v` to `classical_sets.v`
  + lemma `subsetW`, definition `subsetCW`
- in `mathcomp_extra.v`:
  + fix notation `ltLHS`

### Renamed

- in `topology.v`:
  + `open_bigU` -> `bigcup_open`
- in `functions.v`:
  + `mulrfunE` -> `mulrfctE`
  + `scalrfunE` -> `scalrfctE`
  + `exprfunE` -> `exprfctE`
  + `valLr` -> `valR`
  + `valLr_fun` -> `valR_fun`
  + `valLrK` -> `valRK`
  + `oinv_valLr` -> `oinv_valR`
  + `valLr_inj_subproof` -> `valR_inj_subproof`
  + `valLr_surj_subproof` -> `valR_surj_subproof`
- in `measure.v`:
  + `measurable_bigcup` -> `bigcupT_measurable`
  + `measurable_bigcap` -> `bigcapT_measurable`
  + `measurable_bigcup_rat` -> `bigcupT_measurable_rat`
- in `lebesgue_measure.v`:
  + `emeasurable_bigcup` -> `bigcupT_emeasurable`

### Removed

- files `posnum.v` and `nngnum.v` (both subsumed by `signed.v`)
- in `topology.v`:
  + `ltr_distlC`, `ler_distlC`

## [0.4.0] - 2022-03-08

### Added

- in `mathcomp_extra.v`:
  + lemma `all_sig2_cond`
  + definition `olift`
  + lemmas `obindEapp`, `omapEbind`, `omapEapp`, `oappEmap`, `omap_comp`, `oapp_comp`,
    `oapp_comp_f`, `olift_comp`, `compA`, `can_in_pcan`, `pcan_in_inj`, `can_in_comp`,
    `pcan_in_comp`, `ocan_comp`, `pred_omap`, `ocan_in_comp`, `eqbLR`, `eqbRL`
  + definition `opp_fun`, notation `\-`
  + definition `mul_fun`, notation `\*`
  + definition `max_fun`, notation `\max`
  + lemmas `gtr_opp`, `le_le_trans`
  + notations `eqLHS`, `eqRHS`, `leLHS`, `leRHS`, `ltLHS`, `lrRHS`
  + inductive `boxed`
  + lemmas `eq_big_supp`, `perm_big_supp_cond`, `perm_big_supp`
  + lemmma `mulr_ge0_gt0`
  + lemmas `lt_le`, `gt_ge`
  + coercion `pair_of_interval`
  + lemmas `ltBSide`, `leBSide`
  + multirule `lteBSide`
  + lemmas `ltBRight_leBLeft`, `leBRight_ltBLeft`
  + multirule `bnd_simp`
  + lemmas `itv_splitU1`, `itv_split1U`
  + definition `miditv`
  + lemmas `mem_miditv`, `miditv_bnd2`, `miditv_bnd1`
  + lemmas `predC_itvl`, `predC_itvr`, `predC_itv`
- in `boolp.v`:
  + lemmas `cid2`, `propeqP`, `funeqP`, `funeq2P`, `funeq3P`, `predeq2P`,
    `predeq3P`
  + hint `Prop_irrelevance`
  + lemmas `pselectT`, `eq_opE`
  + definition `classicType`, canonicals `classicType_eqType`,
    `classicType_choiceType`, notation `{classic ...}`
  + definition `eclassicType`, canonicals `eclassicType_eqType`,
    `eclassicType_choiceType`, notation `{eclassic ...}`
  + definition `canonical_of`, notations `canonical_`, `canonical`, lemma `canon`
  + lemmas `Peq`, `Pchoice`, `eqPchoice`
  + lemmas `contra_notT`, `contraPT`, `contraTP`, `contraNP`,
    `contraNP`, `contra_neqP`, `contra_eqP`
  + lemmas `forallPNP`, `existsPNP`
  + module `FunOrder`, lemma `lefP`
  + lemmas `meetfE` and `joinfE`
- in `classical_sets.v`:
  + notations `[set: ...]`, ``` *` ```, ``` `* ```
  + definitions `setMR` and `setML`, `disj_set`
  + coercion `set_type`, definition `SigSub`
  + lemmas `set0fun`, `set_mem`, `mem_setT`, `mem_setK`, `set_memK`,
    `memNset`, `setTPn`, `in_set0`, `in_setT`, `in_setC`, `in_setI`,
    `in_setD`, `in_setU`, `in_setM`, `set_valP`, `set_true`, `set_false`, `set_andb`,
    `set_orb`, `fun_true`, `fun_false`, `set_mem_set`, `mem_setE`,
    `setDUK`, `setDUK`, `setDKU`, `setUv`, `setIv`, `setvU`, `setvI`, `setUCK`,
    `setUKC`, `setICK`, `setIKC`, `setDIK`, `setDKI`, `setI1`, `set1I`,
    `subsetT`, `disj_set2E`, `disj_set2P`, `disj_setPS`, `disj_set_sym`,
    `disj_setPCl`, `disj_setPCr`, `disj_setPLR`, `disj_setPRL`, `setF_eq0`,
    `subsetCl`, `subsetCr`, `subsetC2`, `subsetCP`, `subsetCPl`, `subsetCPr`,
    `subsetUl`, `subsetUr`, `setDidl`, `subIsetl`, `subIsetr`, `subDsetl`, `subDsetr`
    `setUKD`, `setUDK`, `setUIDK`, `bigcupM1l`, `bigcupM1r`, `pred_omapE`, `pred_omap_set`
  + hints `subsetUl`, `subsetUr`, `subIsetl`, `subIsetr`, `subDsetl`, `subDsetr`
  + lemmas `image2E`
  + lemmas `Iiota`, `ordII`, `IIord`, `ordIIK`, `IIordK`
  + lemmas `set_imfset`, `imageT`
  + hints `imageP`, `imageT`
  + lemmas `homo_setP`, `image_subP`, `image_sub`, `subset_set2`
  + lemmas `eq_preimage`, `comp_preimage`, `preimage_id`, `preimage_comp`,
    `preimage_setI_eq0`, `preimage0eq`, `preimage0`, `preimage10`,
  + lemmas `some_set0`, `some_set1`, `some_setC`, `some_setR`, `some_setI`, `some_setU`,
    `some_setD`, `sub_image_some`, `sub_image_someP`, `image_some_inj`, `some_set_eq0`,
    `some_preimage`, `some_image`, `disj_set_some`
  + lemmas `some_bigcup`, `some_bigcap`, `bigcup_set_type`, `bigcup_mkcond`,
    `bigcup_mkcondr`, `bigcup_mkcondl`, `bigcap_mkcondr`, `bigcap_mkcondl`,
    `bigcupDr`, `setD_bigcupl`, `bigcup_bigcup_dep`, `bigcup_bigcup`, `bigcupID`.
    `bigcapID`
  + lemmas `bigcup2inE`, `bigcap2`, `bigcap2E`, `bigcap2inE`
  + lemmas `bigcup_sub`, `sub_bigcap`, `subset_bigcup`, `subset_bigcap`, `bigcap_set_type`, `bigcup_pred`
  + lemmas `bigsetU_bigcup2`, `bigsetI_bigcap2`
  + lemmas `in1TT`, `in2TT`, `in3TT`, `inTT_bij`
  + canonical `option_pointedType`
  + notations `[get x | E]`, `[get x : T | E]`
  + variant `squashed`, notation `$| ... |`, tactic notation `squash`
  + definition `unsquash`, lemma `unsquashK`
  + module `Empty` that declares the type `emptyType` with the expected `[emptyType of ...]` notations
  + canonicals `False_emptyType` and `void_emptyType`
  + definitions `no` and `any`
  + lemmas `empty_eq0`
  + definition `quasi_canonical_of`, notations `quasi_canonical_`, `quasi_canonical`, lemma `qcanon`
  + lemmas `choicePpointed`, `eqPpointed`, `Ppointed`
  + lemmas `trivIset_setIl`, `trivIset_setIr`, `sub_trivIset`, `trivIset_bigcup2`
  + definition `smallest`
  + lemmas `sub_smallest`, `smallest_sub`, `smallest_id`
  + lemma and hint `sub_gen_smallest`
  + lemmas `sub_smallest2r`, `sub_smallest2l`
  + lemmas `preimage_itv`, `preimage_itv_o_infty`, `preimage_itv_c_infty`, `preimage_itv_infty_o`,
    `preimage_itv_infty_c`, `notin_setI_preimage`
  + definitions `xsection`, `ysection`
  + lemmas `xsection0`, `ysection0`, `in_xsectionM`, `in_ysectionM`, `notin_xsectionM`, `notin_ysectionM`,
    `xsection_bigcup`, `ysection_bigcup`, `trivIset_xsection`, `trivIset_ysection`, `le_xsection`,
    `le_ysection`, `xsectionD`, `ysectionD`
- in `topology.v`:
  + lemma `filter_pair_set`
  + definition `prod_topo_apply`
  + lemmas `prod_topo_applyE`, `prod_topo_apply_continuous`, `hausdorff_product`
  + lemmas `closedC`, `openC`
  + lemmas `continuous_subspace_in`
  + lemmas`closed_subspaceP`, `closed_subspaceW`, `closure_subspaceW`
  + lemmas `nbhs_subspace_subset`, `continuous_subspaceW`, `nbhs_subspaceT`,
    `continuous_subspaceT_for`, `continuous_subspaceT`, `continuous_open_subspace`
  + globals `subspace_filter`, `subspace_proper_filter`
  + notation `{within ..., continuous ...}`
  + definitions `compact_near`, `precompact`, `locally_compact`
  + lemmas `precompactE`, `precompact_subset`, `compact_precompact`,
    `precompact_closed`
  + definitions `singletons`, `equicontinuous`, `pointwise_precompact`
  + lemmas `equicontinuous_subset`, `equicontinuous_cts`
  + lemmas `pointwise_precomact_subset`, `pointwise_precompact_precompact`
    `uniform_pointwise_compact`, `compact_pointwise_precompact`
  + lemmas `compact_set1`, `uniform_set1`, `ptws_cvg_family_singleton`,
    `ptws_cvg_compact_family`
  + lemmas `connected1`, `connectedU`
  + lemmas `connected_component_sub`, `connected_component_id`,
    `connected_component_out`, `connected_component_max`, `connected_component_refl`,
    `connected_component_cover`, `connected_component_cover`, `connected_component_trans`,
    `same_connected_component`
  + lemma `continuous_is_cvg`
  + lemmas `uniform_limit_continuous`, `uniform_limit_continuous_subspace`
- in `normedtype.v`
  + generalize `IVT` with subspace topology
  + lemmas `abse_continuous`, `cvg_abse`, `is_cvg_abse`, `EFin_lim`, `near_infty_natSinv_expn_lt`
- in `reals.v`:
  + lemmas `sup_gt`, `inf_lt`, `ltr_add_invr`
- in `ereal.v`:
  + lemmas `esum_ninftyP`, `esum_pinftyP`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinftyP`, `desum_ninftyP`
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`
  + lemmas `mule_def_fin`, `mule_def_neq0_infty`, `mule_def_infty_neq0`, `neq0_mule_def`
  + notation `\-` in `ereal_scope` and `ereal_dual_scope`
  + lemma `fin_numB`
  + lemmas `mule_eq_pinfty`, `mule_eq_ninfty`
  + lemmas `fine_eq0`, `abse_eq0`
  + lemmas `EFin_inj`, `EFin_bigcup`, `EFin_setC`, `adde_gt0`, `mule_ge0_gt0`,
    `lte_mul_pinfty`, `lt0R`, `adde_defEninfty`, `lte_pinfty_eq`, `ge0_fin_numE`, `eq_pinftyP`,
  + canonical `mule_monoid`
  + lemmas `preimage_abse_pinfty`, `preimage_abse_ninfty`
  + notation `\-`
  + lemmas `fin_numEn`, `fin_numPn`, `oppe_eq0`, `ltpinfty_adde_def`,
    `gte_opp`, `gte_dopp`, `gt0_mulpinfty`, `lt0_mulpinfty`, `gt0_mulninfty`, `lt0_mulninfty`,
    `eq_infty`, `eq_ninfty`, `hasNub_ereal_sup`, `ereal_sup_EFin`, `ereal_inf_EFin`,
    `restrict_abse`
  + canonical `ereal_pointed`
  + lemma `seq_psume_eq0`
  + lemmas `lte_subl_addl`, `lte_subr_addl`, `lte_subel_addr`,
    `lte_suber_addr`, `lte_suber_addl`, `lee_subl_addl`,
    `lee_subr_addl`, `lee_subel_addr`, `lee_subel_addl`,
    `lee_suber_addr`, `lee_suber_addl`
  + lemmas `lte_dsubl_addl`, `lte_dsubr_addl`, `lte_dsubel_addr`,
    `lte_dsuber_addr`, `lte_dsuber_addl`, `lee_dsubl_addl`,
    `lee_dsubr_addl`, `lee_dsubel_addr`, `lee_dsubel_addl`,
    `lee_dsuber_addr`, `lee_dsuber_addl`
  + lemmas `realDe`, `realDed`, `realMe`, `nadde_eq0`, `padde_eq0`,
    `adde_ss_eq0`, `ndadde_eq0`, `pdadde_eq0`, `dadde_ss_eq0`,
    `mulrpinfty_real`, `mulpinftyr_real`, `mulrninfty_real`,
    `mulninftyr_real`, `mulrinfty_real`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`
  + definition `eseries` with notation `[eseries E]_n`
    + lemmas `eseriesEnat`, `eseriesEord`, `eseriesSr`, `eseriesS`,
      `eseriesSB`, `eseries_addn`, `sub_eseries_geq`, `sub_eseries`,
      `sub_double_eseries`, `eseriesD`
  + definition `etelescope`
  + lemmas `ereal_cvgB`, `nondecreasing_seqD`, `lef_at`
  + lemmas `lim_mkord`, `ereal_pseries_mkcond`, `ereal_pseries_sum`
  + definition `sdrop`
  + lemmas `has_lbound_sdrop`, `has_ubound_sdrop`
  + definitions `sups`, `infs`
  + lemmas `supsN`, `infsN`, `nonincreasing_sups`, `nondecreasing_infs`, `is_cvg_sups`, `is_cvg_infs`,
    `infs_le_sups`, `cvg_sups_inf`, `cvg_infs_sup`, `sups_preimage`, `infs_preimage`, `bounded_fun_has_lbound_sups`,
    `bounded_fun_has_ubound_infs`
  + definitions `lim_sup`, `lim_inf`
  + lemmas `lim_infN`, `lim_supE`, `lim_infE`, `lim_inf_le_lim_sup`, `cvg_lim_inf_sup`,
    `cvg_lim_infE`, `cvg_lim_supE`, `cvg_sups`, `cvg_infs`, `le_lim_supD`, `le_lim_infD`,
    `lim_supD`, `lim_infD`
  + definitions `esups`, `einfs`
  + lemmas `esupsN`, `einfsN`, `nonincreasing_esups`, `nondecreasing_einfs`, `einfs_le_esups`,
    `cvg_esups_inf`, `is_cvg_esups`, `cvg_einfs_sup`, `is_cvg_einfs`, `esups_preimage`, `einfs_preimage`
  + definitions `elim_sup`, `elim_inf`
  + lemmas `elim_infN`, `elim_supN`, `elim_inf_sup`, `elim_inf_sup`, `cvg_ninfty_elim_inf_sup`,
    `cvg_ninfty_einfs`, `cvg_ninfty_esups`, `cvg_pinfty_einfs`, `cvg_pinfty_esups`, `cvg_esups`,
    `cvg_einfs`, `cvg_elim_inf_sup`, `is_cvg_elim_infE`, `is_cvg_elim_supE`
  + lemmas `elim_inf_shift`, `elim_sup_le_cvg`
- in `derive.v`
  + lemma `MVT_segment`
  + lemma `derive1_cst`
- in `realfun.v`:
  + lemma `continuous_subspace_itv`
- in `esum.v` (was `csum.v`):
  + lemmas `sum_fset_set`, `esum_ge`, `esum0`, `le_esum`, `eq_esum`, `esumD`,
    `esum_mkcond`, `esum_mkcondr`, `esum_mkcondl`, `esumID`, `esum_sum`,
    `esum_esum`, `lee_sum_fset_nat`, `lee_sum_fset_lim`, `ereal_pseries_esum`, `reindex_esum`,
    `esum_pred_image`, `esum_set_image`, `esum_bigcupT`
- in `cardinality.v`:
  + notations `#>=`, `#=`, `#!=`
  + scope `card_scope`, delimiter `card`
  + notation `infinite_set`
  + lemmas `injPex`, `surjPex`, `bijPex`, `surjfunPex`, `injfunPex`
  + lemmas `inj_card_le`, `pcard_leP`, `pcard_leTP`, `pcard_injP`, `ppcard_leP`
  + lemmas `pcard_eq`, `pcard_eqP`, `card_bijP`, `card_eqVP`, `card_set_bijP`
  + lemmas `ppcard_eqP`, `card_eqxx`, `inj_card_eq`, `card_some`, `card_image`,
    `card_imsub`
  + hint `card_eq00`
  + lemmas `empty_eq0`, `card_le_emptyl`, `card_le_emptyr`
  + multi-rule `emptyE_subdef`
  + lemmas `card_eq_le`, `card_eqPle`, `card_leT`, `card_image_le`
  + lemmas `card_le_eql`, `card_le_eqr`, `card_eql`, `card_eqr`,
    `card_ge_image`, `card_le_image`, `card_le_image2`, `card_eq_image`, `card_eq_imager`,
    `card_eq_image2`
  + lemmas `card_ge_some`, `card_le_some`, `card_le_some2`, `card_eq_somel`, `card_eq_somer`,
    `card_eq_some2`
  + lemmas `card_eq_emptyr`, `card_eq_emptyl`, `emptyE`
  + lemma and hint `card_setT`
  + lemma and hint `card_setT_sym`
  + lemmas `surj_card_ge`, `pcard_surjP`, `pcard_geP`, `ocard_geP`, `pfcard_geP`
  + lemmas `ocard_eqP`, `oocard_eqP`, `sub_setP`, `card_subP`
  + lemmas `eq_countable`, `countable_set_countMixin`, `countableP`, `sub_countable`
  + lemmas `card_II`, `finite_fsetP`, `finite_subfsetP`, `finite_seqP`, `finite_fset`, `finite_finpred`,
    `finite_finset`, `infiniteP`, `finite_setPn`
  + lemmas `card_le_finite`, `finite_set_leP`, `card_ge_preimage`, `eq_finite_set`,
    `finite_image`
  + lemma and hint `finite_set1`
  + lemmas `finite_setU`, `finite_set2`, `finite_set3`, `finite_set4`, `finite_set5`,
    `finite_set6`, `finite_set7`, `finite_setI`, `finite_setIl`, `finite_setIr`,
    `finite_setM`, `finite_image2`, `finite_image11`
  + definition `fset_set`
  + lemmas `fset_setK`, `in_fset_set`, `fset_set0`, `fset_set1`, `fset_setU`,
    `fset_setI`, `fset_setU1`, `fset_setD`, `fset_setD1`, `fset_setM`
  + definitions `fst_fset`, `snd_fset`, notations ``` .`1 ```, ``` .`2 ```
  + lemmas `finite_set_fst`, `finite_set_snd`, `bigcup_finite`, `finite_setMR`, `finite_setML`,
    `fset_set_II`, `set_fsetK`, `fset_set_inj`, `bigsetU_fset_set`, `bigcup_fset_set`,
    `bigsetU_fset_set_cond`, `bigcup_fset_set_cond`, `bigsetI_fset_set`, `bigcap_fset_set`,
    `super_bij`, `card_eq_fsetP`, `card_IID`, `finite_set_bij`
  + lemmas `countable1`, `countable_fset`
  + lemma and hint `countable_finpred`
  + lemmas `eq_card_nat`
  + canonical `rat_pointedType`
  + lemmas `infinite_rat`, `card_rat`, `choicePcountable`, `eqPcountable`, `Pcountable`,
    `bigcup_countable`, `countableMR`, `countableM`, `countableML`, `infiniteMRl`, `cardMR_eq_nat`
  + mixin `FiniteImage`, structure `FImFun`, notations `{fumfun ... >-> ...}`,
    `[fimfun of ...]`, hint `fimfunP`
  + lemma and hint `fimfun_inP`
  + definitions `fimfun`, `fimfun_key`, canonical `fimfun_keyed`
  + definitions `fimfun_Sub_subproof`, `fimfun_Sub`
  + lemmas `fimfun_rect`, `fimfun_valP`, `fimfuneqP`
  + definitions and canonicals `fimfuneqMixin`, `fimfunchoiceMixin`
  + lemma `finite_image_cst`, `cst_fimfun_subproof`, `fimfun_cst`
  + definition `cst_fimfun`
  + lemma `comp_fimfun_subproof`
  + lemmas `fimfun_zmod_closed`, `fimfunD`, `fimfunN`, `fimfunB`, `fimfun0`, `fimfun_sum`
  + canonicals `fimfun_add`, `fimfun_zmod`, `fimfun_zmodType`
  + definition `fimfun_zmodMixin`
- in `measure.v`:
  + definitions `setC_closed`, `setI_closed`, `setU_closed`, `setD_closed`, `setDI_closed`,
    `fin_bigcap_closed`, `finN0_bigcap_closed`, `fin_bigcup_closed`, `semi_setD_closed`,
    `ndseq_closed`, `trivIset_closed`, `fin_trivIset_closed`, `set_ring`, `sigma_algebra`,
    `dynkin`, `monotone_classes`
  + notations `<<m D, G >>`, `<<m G >>`, `<<s D, G>>`, `<<s G>>`, `<<d G>>`, `<<r G>>`, `<<fu G>>`
  + lemmas `fin_bigcup_closedP`, `finN0_bigcap_closedP`,
    `sedDI_closedP`, `sigma_algebra_bigcap`, `sigma_algebraP`
  + lemma and hint `smallest_sigma_algebra`
  + lemmas `sub_sigma_algebra2`, `sigma_algebra_id`, `sub_sigma_algebra`, `sigma_algebra0`,
    `sigma_algebraD`, `sigma_algebra_bigcup`
  + lemma and hint `smallest_setring`, lemma and hint `setring0`
  + lemmas `sub_setring2`, `setring_id`, `sub_setring`, `setringDI`, `setringU`,
    `setring_fin_bigcup`, `monotone_class_g_salgebra`
  + lemmas `smallest_monotone_classE`, `monotone_class_subset`, `dynkinT`, `dynkinC`, `dynkinU`,
    `dynkin_monotone`, `dynkin_g_dynkin`, `sigma_algebra_dynkin`, `dynkin_setI_bigsetI`,
    `dynkin_setI_sigma_algebra`, `setI_closed_gdynkin_salgebra`
  + factories `isRingOfSets`, `isAlgebraOfSets`
  + lemmas `fin_bigcup_measurable`, `fin_bigcap_measurable`, `sigma_algebra_measurable`,
    `sigma_algebraC`
  + definition `measure_restr`, lemma `measure_restrE`
  + definition `g_measurableType`
  + lemmas `measurable_g_measurableTypeE`
  + lemmas `measurable_fun_id`, `measurable_fun_comp`, `eq_measurable_fun`, `measurable_fun_cst`,
    `measurable_funU`, `measurable_funS`,  `measurable_fun_ext`, `measurable_restrict`
  + definitions `preimage_class` and `image_class`
  + lemmas `preimage_class_measurable_fun`, `sigma_algebra_preimage_class`, `sigma_algebra_image_class`,
    `sigma_algebra_preimage_classE`, `measurability`
  + definition `sub_additive`
  + lemma `semi_additiveW`
  + lemmas `content_fin_bigcup`, `measure_fin_bigcup`, `measure_bigsetU_ord_cond`, `measure_bigsetU_ord`,
  + coercion `measure_to_nadditive_measure`
  + lemmas `measure_semi_bigcup`, `measure_bigcup`
  + hint `measure_ge0`
  + lemma `big_trivIset`
  + defintion `covered_by`
  + module `SetRing`
    * lemmas `ring_measurableE`, `ring_fsets`
    * definition `decomp`
    * lemmas `decomp_triv`, `decomp_triv`, `decomp_neq0`, `decomp_neq0`, `decomp_measurable`, `cover_decomp`,
      `decomp_sub`, `decomp_set0`, `decomp_set0`
    * definition `measure`
    * lemma `Rmu_fin_bigcup`, `RmuE`, `Rmu0`, `Rmu_ge0`, `Rmu_additive`, `Rmu_additive_measure`
    * canonical `measure_additive_measure`
  + lemmas `covered_byP`, `covered_by_finite`, `covered_by_countable`,
    `measure_le0`, `content_sub_additive`, `content_sub_fsum`,
    `content_ring_sup_sigma_additive`, `content_ring_sigma_additive`, `ring_sigma_sub_additive`,
    `ring_sigma_additive`, `measure_sigma_sub_additive`, `measureIl`, `measureIr`,
    `subset_measure0`, `measureUfinr`, `measureUfinl`, `eq_measureU`, `null_set_setU`
  + lemmas `g_salgebra_measure_unique_trace`, `g_salgebra_measure_unique_cover`, `g_salgebra_measure_unique`,
    `measure_unique`, `measurable_mu_extE`, `Rmu_ext`, `measurable_Rmu_extE`,
    `sub_caratheodory`
  + definition `Hahn_ext`, canonical `Hahn_ext_measure`, lemma `Hahn_ext_sigma_finite`, `Hahn_ext_unique`,
    `caratheodory_measurable_mu_ext`
  + definitions `preimage_classes`, `prod_measurable`, `prod_measurableType`
  + lemmas `preimage_classes_comp`, `measurableM`, `measurable_prod_measurableType`, `measurable_prod_g_measurableTypeR`,
    `measurable_prod_g_measurableType`, `prod_measurable_funP`, `measurable_fun_prod1`, `measurable_fun_prod2`
- in `functions.v`:
  + definitions `set_fun`, `set_inj`
  + mixin `isFun`, structure `Fun`, notations `{fun ... >-> ...}`, `[fun of ...]`
    * field `funS` declared as a hint
  + mixin `OInv`, structure `OInversible`, notations `{oinv ... >-> ...}`, `[oinv of ...]`, `'oinv_ ...`
  + structure `OInvFun`, notations `{oinvfun ... >-> ...}`, `[oinvfun of ...]`
  + mixin `OInv_Inv`, factory `Inv`, structure `Inversible`, notations `{inv ... >-> ...}`, `[inv of ...]`, notation `^-1`
  + structure `InvFun`, notations `{invfun ... >-> ...}`, `[invfun of ...]`
  + mixin `OInv_CanV` with field `oinvK` declared as a hint, factory `OCanV`
  + structure `Surject`, notations `{surj ... >-> ...}`, `[surj of ...]`
  + structure `SurjFun`, notations `{surjfun ... >-> ...}`, `[surjfun of ...]`
  + structure `SplitSurj`, notations `{splitsurj ... >-> ...}`, `[splitsurj of ...]`
  + structure `SplitSurjFun`, notations `{splitsurjfun ... >-> ...}`, `[splitsurjfun of ...]`
  + mixin `OInv_Can` with field `funoK` declared as a hint, structure `Inject`, notations `{inj ... >-> ...}`, `[inj of ...]`
  + structure `InjFun`, notations `{injfun ... >-> ...}`, `[injfun of ...]`
  + structure `SplitInj`, notations `{splitinj ... >-> ...}`, `[splitinj of ...]`
  + structure `SplitInjFun`, notations `{splitinjfun ... >-> ...}`, `[splitinjfun of ...]`
  + structure `Bij`, notations `{bij ... >-> ...}`, `[bij of ...]`
  + structure `SplitBij`, notations `{splitbij ... >-> ...}`, `[splitbij of ...]`
  + module `ShortFunSyntax` for shorter notations
  + notation `'funS_ ...`
  + definition and hint `fun_image_sub`
  + definition and hint `mem_fun`
  + notation `'mem_fun_ ...`
  + lemma `some_inv`
  + notation `'oinvS_ ...`
  + variant `oinv_spec`, lemma and hint `oinvP`
  + notation `'oinvP_ ...`
  + lemma and hint `oinvT`, notation `'oinvT_ ...`
  + lemma and hint `invK`, notation `'invK_ ...`
  + lemma and hint `invS`, notation `'invS_ ...`
  + notation `'funoK_ ...`
  + definition `inj` and notation `'inj_ ...`
  + definition and hint `inj_hint`
  + lemma and hint `funK`, notation `'funK_ ...`
  + lemma `funP`
  + factories `Inv_Can`, `Inv_CanV`
  + lemmas `oinvV`, `surjoinv_inj_subproof`, `injoinv_surj_subproof`, `invV`, `oinv_some`,
    `some_canV_subproof`, `some_fun_subproof`, `inv_oapp`, `oinv_oapp`, `inv_oappV`,
    `oapp_can_subproof`, `oapp_surj_subproof`, `oapp_fun_subproof`, `inv_obind`, `oinv_obind`,
    `inv_obindV`, `oinv_comp`, `some_comp_inv`, `inv_comp`, `comp_can_subproof`, `comp_surj_subproof`,
  + notation `'totalfun_ ...`
  + lemmas `oinv_olift`, `inv_omap`, `oinv_omap`, `omapV`
  + factories `canV`, `OInv_Can2`, `OCan2`, `Can`, `Inv_Can2`, `Can2`, `SplitInjFun_CanV`, `BijTT`
  + lemmas `surjective_oinvK`, `surjective_oinvS`, coercion `surjective_ocanV`
  + definition and coercion `surjection_of_surj`, lemma `Psurj`, coercion `surjection_of_surj`
  + lemma `oinv_surj`, lemma and hint `surj`, notation `'surj_`
  + definition `funin`, lemma `set_fun_image`, notation `[fun ... in ...]`
  + definition `split_`, lemmas `splitV`, `splitis_inj_subproof`, `splitid`, `splitsurj_subproof`,
    notation `'split_`, `split`
  + factories `Inj`, `SurjFun_Inj`, `SplitSurjFun_Inj`
  + lemmas `Pinj`, `Pfun`, `injPfun`, `funPinj`, `funPsurj`, `surjPfun`, `Psplitinj`, `funPsplitinj`,
    `PsplitinjT`, `funPsplitsurj`, `PsplitsurjT`
  + definition `unbind`
  + lemmas `unbind_fun_subproof`, `oinv_unbind`, `inv_unbind_subproof`, `inv_unbind`, `unbind_inj_subproof`,
    `unbind_surj_subproof`, `odflt_unbind`, `oinv_val`, `val_bij_subproof`, `inv_insubd`
  + definition `to_setT`, lemma `inv_to_setT`
  + definition `subfun`, lemma `subfun_inj`
  + lemma `subsetW`, definition `subsetCW`
  + lemmas `subfun_imageT`, `subfun_inv_subproof`
  + definition `seteqfun`, lemma `seteqfun_can2_subproof`
  + definitions `incl`, `eqincl`, lemma `eqincl_surj`, notation `inclT`
  + definitions `mkfun`, `mkfun_fun`
  + definition `set_val`, lemmas `oinv_set_val`, `set_valE`
  + definition `ssquash`
  + lemma `set0fun_inj`
  + definitions `finset_val`, `val_finset`
  + lemmas `finset_valK`, `val_finsetK`
  + definition `glue`, `glue1`, `glue2`, lemmas `glue_fun_subproof`, `oinv_glue`, `some_inv_glue_subproof`,
    `inv_glue`, `glueo_can_subproof`, `glue_canv_subproof`
  + lemmas `inv_addr`, `addr_can2_subproof`
  + lemmas `empty_can_subproof`, `empty_fun_subproof`, `empty_canv_subproof`
  + lemmas `subl_surj`, `subr_surj`, `surj_epi`, `epiP`, `image_eq`, `oinv_image_sub`,
    `oinv_Iimage_sub`, `oinv_sub_image`, `inv_image_sub`, `inv_Iimage_sub`, `inv_sub_image`,
    `reindex_bigcup`, `reindex_bigcap`, `bigcap_bigcup`, `trivIset_inj`, `set_bij_homo`
  + definition and hint `fun_set_bij`
  + coercion `set_bij_bijfun`
  + definition and coercion `bij_of_set_bijection`
  + lemma and hint `bij`, notation `'bij_`
  + definition `bijection_of_bijective`, lemmas `PbijTT`, `setTT_bijective`,
    lemma and hint `bijTT`, notation `'bijTT_`
  + lemmas `patchT`, `patchN`, `patchC`, `patch_inj_subproof`,
    `preimage_restrict`, `comp_patch`,
    `patch_setI`, `patch_set0`, `patch_setT`, `restrict_comp`
  + definitions `sigL`, `sigLfun`, `valL_`, `valLfun_`
  + lemmas `sigL_isfun`, `valL_isfun`, `sigLE`, `eq_sigLP`, `eq_sigLfunP`, `sigLK`, `valLK`,
    `valLfunK`, `sigL_valL`, `sigL_valLfun\`, `sigL_restrict`, `image_sigL`, `eq_restrictP`
  + notations `'valL_ ...`, `'valLfun_ ...`, `valL`
  + definitions `sigR`, `valLr`, `valLr_fun`
  + lemmas `sigRK`, `sigR_funK`, `valLrP`, `valLrK`
  + lemmas `oinv_sigL`, `sigL_inj_subproof`, `sigL_surj_subproof`, `oinv_sigR`, `sigR_inj_subproof`,
    `sigR_surj_subproof`, `sigR_some_inv`, `inv_sigR`, `sigL_some_inv`, `inv_sigL`,
    `oinv_valL`, `oapp_comp_x`, `valL_inj_subproof`, `valL_surj_subproof`, `valL_some_inv`,
    `inv_valL`, `sigL_injP`, `sigL_surjP`, `sigL_funP`, `sigL_bijP`, `valL_injP`, `valL_surjP`,
    `valLfunP`, `valL_bijP`
  + lemmas `oinv_valLr`, `valLr_inj_subproof`, `valLr_surj_subproof`
  + definitions `sigLR`, `valLR`, `valLRfun`, lemmas `valLRE`, `valLRfunE`, `sigL2K`,
    `valLRK`, `valLRfun_inj`, `sigLR_injP`, `valLR_injP`, `sigLR_surjP`, `valLR_surjP`,
    `sigLR_bijP`, `sigLRfun_bijP`, `valLR_bijP`, `subsetP`
  + new lemmas `eq_set_bijLR`, `eq_set_bij`, `bij_omap`, `bij_olift`, `bij_sub_sym`,
   `splitbij_sub_sym`, `set_bij00`, `bij_subl`, `bij_sub`, `splitbij_sub`, `can2_bij`,
   `bij_sub_setUrl`, `bij_sub_setUrr`, `bij_sub_setUrr`, `bij_sub_setUlr`
  + definition `pinv_`, lemmas `injpinv_surj`, `injpinv_image`,
    `injpinv_bij`, `surjpK`, `surjpinv_image_sub`, `surjpinv_inj`, `surjpinv_bij`,
    `bijpinv_bij`, `pPbij_`, `pPinj_`, `injpPfun_`, `funpPinj_`
- in `fsbigop.v`:
  + notations `\big[op/idx]_(i \in A) f i`, `\sum_(i \in A) f i`
  + lemma `finite_index_key`
  + definition `finite_support`
  + lemmas `in_finite_support`, `no_finite_support`, `eq_finite_support`
  + variant `finite_support_spec`
  + lemmas  `finite_supportP`, `eq_fsbigl`, `eq_fsbigr`,
    `fsbigTE`, `fsbig_mkcond`, `fsbig_mkcondr`, `fsbig_mkcondl`, `bigfs`,
    `fsbigE`, `fsbig_seq`, `fsbig1`, `fsbig_dflt`, `fsbig_widen`, `fsbig_supp`,
    `fsbig_fwiden`, `fsbig_set0`, `fsbig_set1`, `full_fsbigID`, `fsbigID`, `fsbigU`,
    `fsbigU0`, `fsbigD1`, `full_fsbig_distrr`, `fsbig_distrr`, `mulr_fsumr`, `mulr_fsuml`,
    `fsbig_ord`, `fsbig_finite`, `reindex_fsbig`, `fsbig_image`, `reindex_inside`,
    `reindex_fsbigT`, notation `reindex_inside_setT`
  + lemmas `ge0_mule_fsumr`, `ge0_mule_fsuml`, `fsbigN1`, `fsume_ge0`, `fsume_le0`,
    `fsume_gt0`, `fsume_lt0`, `pfsume_eq0`, `fsbig_setU`, `pair_fsum`, `exchange_fsum`,
    `fsbig_split`
- in `set_interval.v`:
  + definition `neitv`
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itvco`, `set_itvcc`,
    `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`, `set_itv_infty_infty`, `set_itv_o_infty`,
    `set_itv_c_infty`, `set_itv_infty_o`, `set_itv_infty_c`, `set_itv_pinfty_bnd`,
    `set_itv_bnd_ninfty`
  + multirules `set_itv_infty_set0`, `set_itvE`
  + lemmas `setUitv1`, `setU1itv`
  + lemmas `neitvE`, `neitvP`, `setitv0`
  + lemmas `set_itvI`
  + lemmas and hints `has_lbound_itv`, `has_ubound_itv`, `hasNlbound_itv`, `hasNubound_itv`,
    `has_sup_half`, `has_inf_half`
  + lemmas `opp_itv_bnd_infty`, `opp_itvoo`,
    `sup_itv`, `inf_itv`, `sup_itvcc`, `inf_itvcc`
    `setCitvl`, `setCitvr`, `setCitv`
  + lemmas `set_itv_splitD`, `set_itvK`, `RhullT`, `RhullK`,
    `itv_c_inftyEbigcap`, `itv_bnd_inftyEbigcup`, `itv_o_inftyEbigcup`, `set_itv_setT`,
    `set_itv_ge`
  + definitions `conv`, `factor`
  + lemmas `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`, `conv1`, `conv_sym`,
    `conv_flat`, `factorl`, `factorr`, `factor_flat`, `mem_1B_itvcc`, `factorK`,
    `convK`, `conv_inj`, `conv_bij`, `factor_bij`, `leW_conv`, `leW_factor`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`
  + definition `ndconv`
  + lemmas `ndconvE`, `conv_itv_bij`, `conv_itv_bij`, `factor_itv_bij`, `mem_conv_itv`,
    `mem_factor_itv`, `mem_conv_itvcc`, `range_conv`, `range_factor`, `Rhull_smallest`,
    `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`
  + coercion `ereal_of_itv_bound`
  + lemmas `le_bnd_ereal`, `lt_ereal_bnd`, `neitv_bnd1`, `neitv_bnd2`, `Interval_ereal_mem`,
    `ereal_mem_Interval`, `trivIset_set_itv_nth`
  + definition `disjoint_itv`
  + lemmas `disjoint_itvxx`, `lt_disjoint`, `disjoint_neitv`, `disj_itv_Rhull`
- new file `numfun.v`
  + lemmas `restrict_set0`, `restrict_ge0`, `erestrict_set0`, `erestrict_ge0`, `ler_restrict`,
    `lee_restrict`
  + definition `funenng` and notation `^\+`, definition `funennp` and notation `^\-`
  + lemmas and hints `funenng_ge0`, `funennp_ge0`
  + lemmas `funenngN`, `funennpN`, `funenng_restrict`,
    `funennp_restrict`, `ge0_funenngE`, `ge0_funennpE`, `le0_funenngE`, `le0_funennpE`,
    `gt0_funenngM`, `gt0_funennpM`, `lt0_funenngM`, `lt0_funennpM`, `fune_abse`,
    `funenngnnp`, `add_def_funennpg`, `funeD_Dnng`, `funeD_nngD`
  + definition `indic` and notation `\1_`
  + lemmas `indicE`, `indicT`, `indic0`, `indic_restrict`, `restrict_indic`, `preimage_indic`,
    `image_indic`, `image_indic_sub`
- in `trigo.v`:
  + lemmas `acos1`, `acos0`, `acosN1`, `acosN`, `cosKN`, `atan0`, `atan1`
- new file `lebesgue_measure.v`
- new file `lebesgue_integral.v`

### Changed

- in `boolp.v`:
  + `equality_mixin_of_Type`, `choice_of_Type` -> see `classicalType`
- in `topology.v`:
  + generalize `connected_continuous_connected`, `continuous_compact`
  + arguments of `subspace`
  + definition `connected_component`
- in `sequences.v`:
  + `\sum` notations for extended real numbers now in `ereal_scope`
  + lemma `ereal_cvg_sub0` is now an equivalence
- in `derive.v`:
  + generalize `EVT_max`, `EVT_min`, `Rolle`, `MVT`, `ler0_derive1_nincr`,
    `le0r_derive1_ndecr` with subspace topology
  + implicits of `cvg_at_rightE`, `cvg_at_leftE`
- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`
- in `esum.v` (was `csum.v`):
  + lemma `esum_ge0` has now a weaker hypothesis
- notation ``` `I_ ``` moved from `cardinality.v` to `classical_sets.v`
- moved from `classical_types.v` to `boolp.v`:
  + definitions `gen_eq` and `gen_eqMixin`, lemma `gen_eqP`
  + canonicals `arrow_eqType`, `arrow_choiceType`
  + definitions `dep_arrow_eqType`, `dep_arrow_choiceClass`, `dep_arrow_choiceType`
  + canonicals `Prop_eqType`, `Prop_choiceType`
- in `classical_sets.v`:
  + arguments of `preimage`
  + `[set of f]` becomes `range f` (the old notation is still available
     but is displayed as the new one, and will be removed in future versions)
- in `cardinality.v`:
  + definition `card_eq` now uses `{bij ... >-> ...}`
  + definition `card_le` now uses `{injfun ... >-> ...}`
  + definition `set_finite` changed to `finite_set`
  + definition `card_leP` now uses `reflect`
  + definition `card_le0P` now uses `reflect`
  + definition `card_eqP` now uses `reflect`
  + statement of theorem `Cantor_Bernstein`
  + lemma `subset_card_le` does not require finiteness of rhs anymore
  + lemma `surjective_card_le` does not require finiteness of rhs anymore and renamed to `surj_card_ge`
  + lemma `card_le_diff` does not require finiteness of rhs anymore and renamed to `card_le_setD`
  + lemma `card_eq_sym` now an equality
  + lemma `card_eq0` now an equality
  + lemmas `card_le_II` and `card_eq_II` now equalities
  + lemma `countable_injective` renamed to `countable_injP` and use `reflect`
  + lemmas `II0`, `II1`, `IIn_eq0` moved to `classical_sets.v`
  + lemma `II_recr` renamed to `IIS` and moved to `classical_sets.v`
  + definition `surjective` moved to `functions.v` and renamed `set_surj`
  + definition `set_bijective` moved to `functions.v` and changed to `set_bij`
  + lemma `surjective_id` moved to `functions.v` and renamed `surj_id`
  + lemma `surjective_set0` moved to `functions.v` and renamed `surj_set0`
  + lemma `surjectiveE` moved to `functions.v` and renamed `surjE`
  + lemma `surj_image_eq` moved to `functions.v`
  + lemma `can_surjective` moved to `functions.v` and changed to `can_surj`
  + lemma `surjective_comp` moved to `functions.v` and renamed `surj_comp`
  + lemma `set_bijective1` moved to `functions.v` and renamed `eq_set_bijRL`
  + lemma `set_bijective_image` moved to `functions.v` and renamed `inj_bij`
  + lemma `set_bijective_subset` moved to `functions.v` and changed to `bij_subr`
  + lemma `set_bijective_comp` moved to `functions.v` and renamed `set_bij_comp`
  + definition `inverse` changed to `pinv_`, see `functions.v`
  + lemma `inj_of_bij` moved to `functions.v` and renamed to `set_bij_inj`
  + lemma `sur_of_bij` moved to `functions.v` and renamed to `set_bij_surj`
  + lemma `sub_of_bij` moved to `functions.v` and renamed to `set_bij_sub`
  + lemma `set_bijective_D1` moved to `functions.v` and renamed to `bij_II_D1`
  + lemma `injective_left_inverse` moved to `functions.v` and changed to `pinvKV`
  + lemma `injective_right_inverse` moved to `functions.v` and changed to `pinvK`
  + lemmas `image_nat_maximum`, `fset_nat_maximum` moved to `mathcomp_extra.v`
  + lemmas `enum0`, `enum_recr` moved to `mathcomp_extra.v` and renamed to `enum_ord0`, `enum_ordS`
  + lemma `in_inj_comp` moved to `mathcomp_extra.v`
- from `cardinality.v` to `classical_sets.v`:
  + `eq_set0_nil` -> `set_seq_eq0`
  + `eq_set0_fset0` -> `set_fset_eq0`
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`  moved to `classical_sets.v`
  + mixin `isSemiRingOfSets` and `isRingOfSets` changed
  + types `semiRingOfSetsType`, `ringOfSetsType`, `algebraOfSetsType`, `measurableType` now pointed types
  + definition `measurable_fun` changed
  + definition `sigma_sub_additive` changed and renamed to `sigma_subadditive`
  + record `AdditiveMeasure.axioms`
  + lemmas `measure_ge0`
  + record `Measure.axioms`
  + definitions `seqDU`, `seqD`, lemma and hint `trivIset_seqDU`, lemmas `bigsetU_seqDU`, `seqDU_bigcup_eq`,
    `seqDUE`, `trivIset_seqD`, `bigsetU_seqD`, `setU_seqD`, `eq_bigsetU_seqD`, `eq_bigcup_seqD`, `eq_bigcup_seqD_bigsetU`
    moved to `sequences.v`
  + definition `negligibleP` weakened to additive measures
  + lemma `measure_negligible`
  + definition `caratheodory_measurable` and `caratheodory_type` weakened from outer measures to functions
  + lemma `caratheodory_measure_ge0` does take a condition anymore
  + definitions `measurable_cover` and `mu_ext`, canonical `outer_measure_of_measure` weakened to `semiRingOfSetsType`
- in `ereal.v`:
  + lemmas `abse_ge0`, `gee0_abs`, `gte0_abs`, `lee0_abs`, `lte0_abs`,
    `mulN1e`, `muleN1` are generalized from `realDomainType` to
    `numDomainType`
- moved from `normedtype.v` to `mathcomp_extra.v`:
  + lemmas `ler_addgt0Pr`, `ler_addgt0Pl`, `in_segment_addgt0Pr`, `in_segment_addgt0Pl`,
- moved from `posnum.v` to `mathcomp_extra.v`:
  + lemma `splitr`
- moved from `measure.v` to `sequences.v`
  + lemma `cvg_geometric_series_half`
  + lemmas `realDe`, `realDed`, `realMe`, `nadde_eq0`, `padde_eq0`,
    `adde_ss_eq0`, `ndadde_eq0`, `pdadde_eq0`, `dadde_ss_eq0`,
    `mulrpinfty_real`, `mulpinftyr_real`, `mulrninfty_real`,
    `mulninftyr_real`, `mulrinfty_real`
- moved from `topology.v` to `functions.v`
  + section `function_space` (defintion `cst`, definition `fct_zmodMixin`,
    canonical `fct_zmodType`, definition `fct_ringMixin`, canonical `fct_ringType`,
    canonical `fct_comRingType`, definition `fct_lmodMixin`, canonical `fct_lmodType`,
    lemma `fct_lmodType`)
  + lemmas `addrfunE`, `opprfunE`, `mulrfunE`, `scalrfunE`, `cstE`, `exprfunE`, `compE`
  + definition `fctE`
- moved from `classical_sets.v` to `functions.v`
  + definition `patch`,	notation `restrict` and `f \_ D`

### Renamed

- in `topology.v`:
  + `closedC` -> `open_closedC`
  + `openC` -> `closed_openC`
  + `cvg_restrict_dep` -> `cvg_sigL`
- in `classical_sets.v`:
  + `mkset_nil` -> `set_nil`
- in `cardinality.v`:
  + `card_le0x` -> `card_ge0`
  + `card_eq_sym` -> `card_esym`
  + `set_finiteP` -> `finite_setP`
  + `set_finite0` -> `finite_set0`
  + `set_finite_seq` -> `finite_seq`
  + `set_finite_countable` -> `finite_set_countable`
  + `subset_set_finite` -> `sub_finite_set`
  + `set_finite_preimage` -> `finite_preimage`
  + `set_finite_diff` -> `finite_setD`
  + `countably_infinite_prod_nat` -> `card_nat2`
- file `csum.v` renamed to `esum.v` with the following renamings:
  + `\csum` -> `\esum`
  + `csum` -> `esum`
  + `csum0` -> `esum_set0`
  + `csum_ge0` -> `esum_ge0`
  + `csum_fset` -> `esum_fset`
  + `csum_image` -> `esum_image`
  + `csum_bigcup` -> `esum_bigcup`
- in `ereal.v`:
  + `lte_subl_addl` -> `lte_subel_addl`
  + `lte_subr_addr` -> `lte_suber_addr`
  + `lte_dsubl_addl` -> `lte_dsubel_addl`
  + `lte_dsubr_addr` -> `lte_dsuber_addr`

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`
  + lemmas `big_nat_widenl`, `big_geq_mkord`
- in `csum.v`:
  + lemmas `fsets_img`, `fsets_ord`, `fsets_ord_nat`, `fsets_ord_subset`, `csum_bigcup_le`,
    `le_csum_bigcup`
- in `classical_sets.v`:
  + lemma `subsetU`
  + definition `restrict_dep`, `extend_up`, lemma `restrict_depE`
- in `cardinality.v`:
  + lemma `surjective_image`, `surjective_image_eq0`
  + lemma `surjective_right_inverse`,
  + lemmas `card_le_surj`, `card_eq00`
  + lemmas `card_eqTT`, `card_eq_II`, `card_eq_le`, `card_leP`
  + lemmas `set_bijective_inverse`, `countable_trans`, `set_bijective_U1`,
    `set_bijective_cyclic_shift`, `set_bijective_cyclic_shift_simple`, `set_finite_bijective`,
    `subset_set_finite_card_le`, `injective_set_finite_card_le`, `injective_set_finite`,
    `injective_card_le`, `surjective_set_finite_card_le`, `set_finite_inter_set0_union`,
    `ex_in_D`.
  + definitions `min_of_D`, `min_of_D_seq`, `infsub_enum`
  + lemmas `min_of_D_seqE`, `increasing_infsub_enum`, `sorted_infsub_enum`, `injective_infsub_enum`,
    `subset_infsub_enum`, `infinite_nat_subset_countable`
  + definition `enumeration`
  + lemmas `enumeration_id`, `enumeration_set0`, `ex_enum_notin`
  + defnitions `min_of_e`, `min_of_e_seq`, `smallest_of_e`, `enum_wo_rep`
  + lemmas `enum_wo_repE`, `min_of_e_seqE`,
    `smallest_of_e_notin_enum_wo_rep`, `injective_enum_wo_rep`, `surjective_enum_wo_rep`,
    `set_bijective_enum_wo_rep`, `enumeration_enum_wo_rep`, `countable_enumeration`
  + definition `nat_of_pair`
  + lemmas `nat_of_pair_inj`, `countable_prod_nat`
- in `measure.v`:
  + definition `diff_fsets`
  + lemmas `semiRingOfSets_measurableI`, `semiRingOfSets_measurableD`, `semiRingOfSets_diff_fsetsE`,
    `semiRingOfSets_diff_fsets_disjoint`
  + definition `uncurry`
- in `sequences.v`:
  + lemmas `leq_fact`, `prod_rev`, `fact_split` (now in MathComp)
- in `boolp.v`
  + module BoolQuant with notations `` `[forall x P] `` and `` `[exists x P] ``
    (subsumed by `` `[< >] ``)
  + definition `xchooseb`
  + lemmas `existsPP`, `forallPP`, `existsbP`, `forallbP`, `forallbE`,
    `existsp_asboolP`, `forallp_asboolP`, `xchoosebP`, `imsetbP`
- in `normedtype.v`:
  + lemmas `nbhs_pinfty_gt_pos`, `nbhs_pinfty_ge_pos`, `nbhs_ninfty_lt_pos`,
    `nbhs_ninfty_le_pos`

## [0.3.13] - 2022-01-24

### Added

- in `topology.v`:
  + definitions `kolmogorov_space`, `accessible_space`
  + lemmas `accessible_closed_set1`, `accessible_kolmogorov`
  + lemma `filter_pair_set`
  + definition `prod_topo_apply`
  + lemmas `prod_topo_applyE`, `prod_topo_apply_continuous`, `hausdorff_product`
- in `ereal.v`:
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`
  + lemmas `mule_def_fin`, `mule_def_neq0_infty`, `mule_def_infty_neq0`, `neq0_mule_def`
  + notation `\-` in `ereal_scope` and `ereal_dual_scope`
  + lemma `fin_numB`
  + lemmas `mule_eq_pinfty`, `mule_eq_ninfty`
  + lemmas `fine_eq0`, `abse_eq0`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`

### Changed

- in `topology.v`:
  + renamed and generalized `setC_subset_set1C` implication to
    equivalence `subsetC1`
- in `ereal.v`:
  + lemmas `ereal_sup_gt`, `ereal_inf_lt` now use `exists2`
- notation `\*` moved from `realseq.v` to `topology.v`

### Renamed

- in `topology.v:
  + `hausdorff` -> `hausdorff_space`

### Removed

- in `realseq.v`:
  + notation `\-`

### Infrastructure

- add `.dir-locals.el` for company-coq symbols

## [0.3.12] - 2021-12-29

### Added

- in `boolp.v`:
  + lemmas `not_True`, `not_False`
- in `classical_sets.v`:
  + lemma `setDIr`
  + lemmas `setMT`, `setTM`, `setMI`
  + lemmas `setSM`, `setM_bigcupr`, `setM_bigcupl`
  + lemmas `cover_restr`, `eqcover_r`
  + lemma `notin_set`
- in `reals.v`:
  + lemma `has_ub_lbN`
- in `ereal.v`:
  + lemma `onee_eq0`
  + lemma `EFinB`
  + lemmas `mule_eq0`, `mule_lt0_lt0`, `mule_gt0_lt0`, `mule_lt0_gt0`,
    `pmule_rge0`, `pmule_lge0`, `nmule_lge0`, `nmule_rge0`,
    `pmule_rgt0`, `pmule_lgt0`, `nmule_lgt0`, `nmule_rgt0`
  + lemmas `muleBr`, `muleBl`
  + lemma `eqe_absl`
  + lemma `lee_pmul`
  + lemmas `fin_numElt`, `fin_numPlt`
- in `topology.v`
  + lemmas `cstE`, `compE`, `opprfunE`, `addrfunE`, `mulrfunE`, `scalrfunE`, `exprfunE`
  + multi-rule `fctE`
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
- in `normedtype.v`
  + lemmas `continuous_shift`, `continuous_withinNshiftx`
  + lemmas `bounded_fun_has_ubound`, `bounded_funN`, `bounded_fun_has_lbound`,
    `bounded_funD`
- in `derive.v`
  + lemmas `derive1_comp`, `derivable_cst`, `derivable_id`, trigger_derive`
  + instances `is_derive_id`, `is_derive_Nid`
- in `sequences.v`:
  + lemmas `cvg_series_bounded`, `cvg_to_0_linear`, `lim_cvg_to_0_linear`.
  + lemma `cvg_sub0`
  + lemma `cvg_zero`
  + lemmas `ereal_cvg_abs0`, `ereal_cvg_sub0`, `ereal_squeeze`
  + lemma `ereal_is_cvgD`
- in `measure.v`:
  + hints for `measurable0` and `measurableT`
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
  + lemmas `cosK`, `sin_acos`, `continuous_acos`, `is_derive1_acos`
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
  + statements of lemmas `nondecreasing_cvg`, `nondecreasing_is_cvg`,
    `nonincreasing_cvg`, `nonincreasing_is_cvg` use `has_{l,u}bound`
    predicates instead of requiring an additional variable
  + statement of lemma `S1_sup` use `ubound` instead of requiring an
    additional variable

### Renamed

- in `normedtype.v`:
  + `nbhs_minfty_lt_real` -> `nbhs_ninfty_lt`
  + `nbhs_minfty_le_real` -> `nbhs_ninfty_le`
- in `sequences.v`:
  + `cvgNminfty` -> `cvgNninfty`
  + `cvgPminfty` -> `cvgPninfty`
  + `ler_cvg_minfty` -> `ler_cvg_ninfty`
  + `nondecreasing_seq_ereal_cvg` -> `ereal_nondecreasing_cvg`
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

### Removed

- in `ereal.v`:
  + lemma `subEFin`

### Infrastructure

- in `Makefile.common`
  + add `doc` and `doc-clean` targets

## [0.3.11] - 2021-11-14

### Added

- in `boolp.v`:
  + lemmas `orA`, `andA`
- in `classical_sets.v`
  + lemma `setC_inj`,
  + lemma `setD1K`,
  + lemma `subTset`,
  + lemma `setUidPr`, `setUidl` and `setUidr`,
  + lemma `setIidPr`, `setIidl` and `setIidr`,
  + lemma `set_fset0`, `set_fset1`, `set_fsetI`, `set_fsetU`,
  + lemma `bigcap_inf`, `subset_bigcup_r`, `subset_bigcap_r`,
    `eq_bigcupl`, `eq_bigcapl`, `eq_bigcup`, `eq_bigcap`, `bigcupU`,
    `bigcapI`, `bigcup_const`, `bigcap_const`, `bigcapIr`, `bigcupUr`,
    `bigcap_set0`, `bigcap_set1`, `bigcap0`, `bigcapT`, `bigcupT`,
    `bigcapTP`, `setI_bigcupl`, `setU_bigcapl`, `bigcup_mkcond`,
    `bigcap_mkcond`, `setC_bigsetU`, `setC_bigsetI`,
    `bigcap_set_cond`, `bigcap_set`, `bigcap_split`, `bigcap_mkord`,
    `subset_bigsetI`, `subset_bigsetI_cond`, `bigcap_image`
  + lemmas `bigcup_setU1`, `bigcap_setU1`, `bigcup_setU`,
    `bigcap_setU`, `bigcup_fset`, `bigcap_fset`, `bigcup_fsetU1`,
    `bigcap_fsetU1`, `bigcup_fsetD1`, `bigcap_fsetD1`,
  + definition `mem_set : A u -> u \in A`
  + lemmas `in_setP` and `in_set2P`
  + lemma `forall_sig`
  + definition `patch`, notation `restrict` and `f \_ D`, definitions
    `restrict_dep` and `extend_dep`, with lemmas `restrict_depE`,
    `fun_eq_inP`, `extend_restrict_dep`, `extend_depK`,
    `restrict_extend_dep`, `restrict_dep_restrict`,
    `restrict_dep_setT`
  + lemmas `setUS`, `setSU`, `setUSS`, `setUCA`, `setUAC`, `setUACA`,
    `setUUl`, `setUUr`
  + lemmas `bigcup_image`, `bigcup_of_set1`, `set_fset0`, `set_fset1`, `set_fsetI`,
    `set_fsetU`, `set_fsetU1`, `set_fsetD`, `set_fsetD1`,
  + notation `` [set` i] ``
  + notations `set_itv`, `` `[a, b] ``, `` `]a, b] ``, `` `[a, b[ ``,
    `` `]a, b[ ``, `` `]-oo, b] ``, `` `]-oo, b[ ``, `` `[a, +oo] ``,
    `` `]a, +oo] ``, `` `]-oo, +oo[ ``
  + lemmas `setDDl`, `setDDr`
- in `topology.v`:
  + lemma `fmap_comp`
  + definition `finSubCover`
  + notations ``{uniform` A -> V }`` and `{uniform U -> V}` and their
    canonical structures of uniform type.
  + definition `uniform_fun` to cast into
  + notations `{uniform A, F --> f }` and `{uniform, F --> f}`
  + lemma `uniform_cvgE`
  + lemma `uniform_nbhs`
  + notation `{ptws U -> V}` and its canonical structure of
    topological type,
  + definition `ptws_fun`
  + notation `{ptws F --> f }`
  + lemma `ptws_cvgE`
  + lemma `ptws_uniform_cvg`
  + lemma `cvg_restrict_dep`
  + lemma `eq_in_close`
  + lemma `hausdorrf_close_eq_in`
  + lemma `uniform_subset_nbhs`
  + lemma `uniform_subset_cvg`
  + lemma `uniform_restrict_cvg`
  + lemma `cvg_uniformU`
  + lemma `cvg_uniform_set0`
  + notation `{family fam, U -> V}` and its canonical structure of
    topological type
  + notation `{family fam, F --> f}`
  + lemma `fam_cvgP`
  + lemma `fam_cvgE`
  + definition `compactly_in`
  + lemma `family_cvg_subset`
  + lemma `family_cvg_finite_covers`
  + lemma `compact_cvg_within_compact`
  + lemma `le_bigmax`
  + definition `monotonous`
  + lemma `and_prop_in`
  + lemmas `mem_inc_segment`, `mem_dec_segment`
  + lemmas `ltr_distlC`, `ler_distlC`
  + lemmas `subset_ball_prop_in_itv`, `subset_ball_prop_in_itvcc`
  + lemma `dense_rat`
- in `normedtype.v`:
  + lemma `is_intervalPlt`
  + lemma `mule_continuous`
  + lemmas `ereal_is_cvgN`, `ereal_cvgZr`, `ereal_is_cvgZr`, `ereal_cvgZl`, `ereal_is_cvgZl`,
    `ereal_limZr`, `ereal_limZl`, `ereal_limN`
  + lemma `bound_itvE`
  + lemmas `nearN`, `near_in_itv`
  + lemmas `itvxx`, `itvxxP`, `subset_itv_oo_cc`
  + lemma `at_right_in_segment`
  + notations ``f @`[a, b]``, ``g @`]a , b[``
  + lemmas `mono_mem_image_segment`, `mono_mem_image_itvoo`, `mono_surj_image_segment`,
    `inc_segment_image`, `dec_segment_image`, `inc_surj_image_segment`, `dec_surj_image_segment`,
    `inc_surj_image_segmentP`, `dec_surj_image_segmentP`, ``mono_surj_image_segmentP``
- in `reals.v`:
  + lemmas `floor1`, `floor_neq0`
  + lemma `int_lbound_has_minimum`
  + lemma `rat_in_itvoo`
- in `ereal.v`:
  + notation `x +? y` for `adde_def x y`
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
  + lemmas `adde_le0`, `sume_le0`, `oppe_ge0`, `oppe_le0`,
    `lte_opp`, `gee_addl`, `gee_addr`, `lte_addr`,
    `gte_subl`, `gte_subr`, `lte_le_sub`, `lee_sum_npos_subset`,
    `lee_sum_npos`, `lee_sum_npos_ord`, `lee_sum_npos_natr`,
    `lee_sum_npos_natl`, `lee_sum_npos_subfset`, `lee_opp`,
    `le0_muleDl`, `le0_muleDr`, `le0_sume_distrl`, `le0_sume_distrr`,
    `adde_defNN`, `minEFin`, `mine_ninftyl`, `mine_ninftyr`, `mine_pinftyl`,
    `mine_pinftyr`, `oppe_max`, `oppe_min`, `mineMr`, `mineMl`
  + definitions `dual_adde`
  + notations for the above in scope `ereal_dual_scope` delimited by `dE`
  + lemmas `dual_addeE`, `dual_sumeE`, `dual_addeE_def`, `daddEFin`,
    `dsumEFin`, `dsubEFin`, `dadde0`, `dadd0e`, `daddeC`, `daddeA`,
    `daddeAC`, `daddeCA`, `daddeACA`, `doppeD`, `dsube0`, `dsub0e`, `daddeK`,
    `dfin_numD`, `dfineD`, `dsubeK`, `dsube_eq`,
    `dsubee`, `dadde_eq_pinfty`, `daddooe`, `dadde_Neq_pinfty`,
    `dadde_Neq_ninfty`, `desum_fset_pinfty`, `desum_pinfty`,
    `desum_fset_ninfty`, `desum_ninfty`, `dadde_ge0`, `dadde_le0`,
    `dsume_ge0`, `dsume_le0`, `dsube_lt0`, `dsubre_le0`,
    `dsuber_le0`, `dsube_ge0`, `lte_dadd`, `lee_daddl`, `lee_daddr`,
    `gee_daddl`, `gee_daddr`, `lte_daddl`, `lte_daddr`, `gte_dsubl`,
    `gte_dsubr`, `lte_dadd2lE`, `lee_dadd2l`, `lee_dadd2lE`,
    `lee_dadd2r`, `lee_dadd`, `lte_le_dadd`, `lee_dsub`,
    `lte_le_dsub`, `lee_dsum`, `lee_dsum_nneg_subset`,
    `lee_dsum_npos_subset`, `lee_dsum_nneg`, `lee_dsum_npos`,
    `lee_dsum_nneg_ord`, `lee_dsum_npos_ord`, `lee_dsum_nneg_natr`,
    `lee_dsum_npos_natr`, `lee_dsum_nneg_natl`, `lee_dsum_npos_natl`,
    `lee_dsum_nneg_subfset`, `lee_dsum_npos_subfset`,
    `lte_dsubl_addr`, `lte_dsubl_addl`, `lte_dsubr_addr`,
    `lee_dsubr_addr`, `lee_dsubl_addr`, `ge0_dsume_distrl`, `dmulrEDr`,
    `dmulrEDl`, `dge0_mulreDr`, `dge0_mulreDl`, `dle0_mulreDr`, `dle0_mulreDl`,
    `ge0_dsume_distrr`, `le0_dsume_distrl`, `le0_dsume_distrr`,
    `lee_abs_dadd`, `lee_abs_dsum`, `lee_abs_dsub`, `dadde_minl`, `dadde_minr`,
    `lee_dadde`, `lte_spdaddr`
  + lemmas `abse0`, `abse_ge0`, `lee_abs`, `abse_id`, `lee_abs_add`, `lee_abs_sum`,
    `lee_abs_sub`, `gee0_abs`, `gte0_abs`, `lee_abs`, `lte0_abs`, `abseM`, `lte_absl`,
    `eqe_absl`
  + notations `maxe`, `mine`
  + lemmas `maxEFin`, `adde_maxl`, `adde_maxr`,
    `maxe_pinftyl`, `maxe_pinftyr`, `maxe_ninftyl`, `maxe_ninftyr`
  + lemmas `sub0e`, `lee_wpmul2r`, `mule_ninfty_ninfty`
  + lemmas `sube_eq` `lte_pmul2r`, `lte_pmul2l`, `lte_nmul2l`, `lte_nmul2r`, `mule_le0`,
    `pmule_llt0`, `pmule_rlt0`, `nmule_llt0`, `nmule_rlt0`, `mule_lt0`
  + lemmas `maxeMl`, `maxeMr`
  + lemmas `lte_0_pinfty`, `lte_ninfty_0`, `lee_0_pinfty`, `lee_ninfty_0`,
    `oppe_gt0`, `oppe_lt0`
  + lemma `telescope_sume`
  + lemmas `lte_add_pinfty`, `lte_sum_pinfty`
- in `cardinality.v`:
  + definition `nat_of_pair`, lemma `nat_of_pair_inj`
  + lemmas `surjectiveE`, `surj_image_eq`, `can_surjective`
- in `sequences.v`:
  + lemmas `lt_lim`, `nondecreasing_dvg_lt`, `ereal_lim_sum`
  + lemmas `ereal_nondecreasing_opp`, `ereal_nondecreasing_is_cvg`, `ereal_nonincreasing_cvg`,
    `ereal_nonincreasing_is_cvg`
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
- in `measure.v`:
  + definition `seqDU`
  + lemmas `trivIset_seqDU`, `bigsetU_seqDU`, `seqDU_bigcup_eq`, `seqDUE`
  + lemmas `bigcup_measurable`, `bigcap_measurable`, `bigsetI_measurable`

### Changed

- in `classical_sets.v`
  + `setU_bigcup` -> `bigcupUl` and reversed
  + `setI_bigcap` -> `bigcapIl` and reversed
  + removed spurious disjunction in `bigcup0P`
  + `bigcup_ord` -> `bigcup_mkord` and reversed
  + `bigcup_of_set1` -> `bigcup_imset1`
  + `bigcupD1` -> `bigcup_setD1` and `bigcapD1` -> `bigcap_setD1` and
    rephrased using ``P `\ x`` instead of ``P `&` ~` [set x]``
  + order of arguments for `setIS`, `setSI`, `setUS`, `setSU`, `setSD`, `setDS`
  + generalize lemma `perm_eq_trivIset`
- in `topology.v`:
  + replace `closed_cvg_loc` and `closed_cvg` by a more general lemma `closed_cvg`
- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`
  + definition `is_interval`
  + the following lemmas have been generalized to `orderType`,
    renamed as follows, moved out of the module `BigmaxBigminr`
    to `topology.v`:
    * `bigmaxr_mkcond` -> `bigmax_mkcond`
    * `bigmaxr_split` -> `bigmax_split`
    * `bigmaxr_idl` -> `bigmax_idl`
    * `bigmaxrID` -> `bigmaxID`
    * `bigmaxr_seq1` -> `bigmax_seq1`
    * `bigmaxr_pred1_eq` -> `bigmax_pred1_eq`
    * `bigmaxr_pred1` -> `bigmax_pred1`
    * `bigmaxrD1` -> `bigmaxD1`
    * `ler_bigmaxr_cond`  -> `ler_bigmax_cond `
    * `ler_bigmaxr` -> `ler_bigmax`
    * `bigmaxr_lerP` -> `bigmax_lerP`
    * `bigmaxr_sup` -> `bigmax_sup`
    * `bigmaxr_ltrP` -> `bigmax_ltrP`
    * `bigmaxr_gerP` -> `bigmax_gerP`
    * `bigmaxr_eq_arg` -> `bigmax_eq_arg`
    * `bigmaxr_gtrP` -> `bigmax_gtrP`
    * `eq_bigmaxr` -> `eq_bigmax`
    * module `BigmaxBigminr` -> `Bigminr`
- in `ereal.v`:
  + change definition `mule` such that 0 x oo = 0
  + `adde` now defined using `nosimpl` and `adde_subdef`
  + `mule` now defined using `nosimpl` and `mule_subdef`
  + lemmas `lte_addl`, `lte_subl_addr`, `lte_subl_addl`, `lte_subr_addr`,
    `lte_subr_addr`, `lte_subr_addr`, `lb_ereal_inf_adherent`
  + `oppeD` to use `fin_num`
  + weaken `realDomainType` to `numDomainType` in `mule_ninfty_pinfty`,
    `mule_pinfty_ninfty`, `mule_pinfty_pinfty`, `mule_ninfty_ninfty`,
    `mule_neq0`, `mule_ge0`, `mule_le0`, `mule_gt0`, `mule_le0_ge0`,
    `mule_ge0_le0`
- in `reals.v`:
  + generalize from `realType` to `realDomainType` lemmas
    `has_ub_image_norm`, `has_inf_supN`
- in `sequences.v`:
  + generalize from `realType` to `realFieldType` lemmas
    `cvg_has_ub`, `cvg_has_sup`, `cvg_has_inf`
  + change the statements of `cvgPpinfty`, `cvgPminfty`,
    `cvgPpinfty_lt`
  + generalize `nondecreasing_seqP`, `nonincreasing_seqP`, `increasing_seqP`,
    `decreasing_seqP` to equivalences
  + generalize `lee_lim`, `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`,
    `ereal_cvgD`, `ereal_limD`, `ereal_pseries0`, `eq_ereal_pseries` from `realType` to `realFieldType`
  + lemma `ereal_pseries_pred0` moved from `csum.v`, minor generalization
- in `landau.v`:
  + lemma `cvg_shift` renamed to `cvg_comp_shift` and moved to `normedtype.v`
- in `measure.v`:
  + lemmas `measureDI`, `measureD`, `sigma_finiteP`
- `exist_congr` -> `eq_exist` and moved from `classsical_sets.v` to
  `boolp.v`
- `predeqP` moved from `classsical_sets.v` to `boolp.v`
- moved from `landau.v` to `normedtype.v`:
  + lemmas `comp_shiftK`, `comp_centerK`, `shift0`, `center0`, `near_shift`,
    `cvg_shift`
- lemma `exists2P` moved from `topology.v` to `boolp.v`
- move from `sequences.v` to `normedtype.v` and generalize from `nat` to `T : topologicalType`
  + lemmas `ereal_cvgN`

### Renamed

- in `classical_sets.v`
  + `eqbigcup_r` -> `eq_bigcupr`
  + `eqbigcap_r` -> `eq_bigcapr`
  + `bigcup_distrr` -> `setI_bigcupr`
  + `bigcup_distrl` -> `setI_bigcupl`
  + `bigcup_refl` -> `bigcup_splitn`
  + `setMT` -> `setMTT`
- in `ereal.v`:
  + `adde` -> `adde_subdef`
  + `mule` -> `mule_subdef`
  + `real_of_extended` -> `fine`
  + `real_of_extendedN` -> `fineN`
  + `real_of_extendedD` -> `fineD`
  + `EFin_real_of_extended` -> `fineK`
  + `real_of_extended_expand` -> `fine_expand`
- in `sequences.v`:
  + `nondecreasing_seq_ereal_cvg` -> `nondecreasing_ereal_cvg`
- in `topology.v`:
  + `nbhs'` -> `dnbhs`
  + `nbhsE'` -> `dnbhs`
  + `nbhs'_filter` -> `dnbhs_filter`
  + `nbhs'_filter_on` -> `dnbhs_filter_on`
  + `nbhs_nbhs'` -> `nbhs_dnbhs`
  + `Proper_nbhs'_regular_numFieldType` -> `Proper_dnbhs_regular_numFieldType`
  + `Proper_nbhs'_numFieldType` -> `Proper_dnbhs_numFieldType`
  + `ereal_nbhs'` -> `ereal_dnbhs`
  + `ereal_nbhs'_filter` -> `ereal_dnbhs_filter`
  + `ereal_nbhs'_le` -> `ereal_dnbhs_le`
  + `ereal_nbhs'_le_finite` -> `ereal_dnbhs_le_finite`
  + `Proper_nbhs'_numFieldType` -> `Proper_dnbhs_numFieldType`
  + `Proper_nbhs'_realType` -> `Proper_dnbhs_realType`
  + `nbhs'0_lt` -> `dnbhs0_lt`
  + `nbhs'0_le` -> `dnbhs0_le`
  + `continuity_pt_nbhs'` -> `continuity_pt_dnbhs`
- in `measure.v`:
  + `measure_additive2` -> `measureU`
  + `measure_additive` -> `measure_bigcup`

### Removed

- in `boolp.v`:
  + definition `PredType`
  + local notation `predOfType`
- in `nngnum.v`:
  + module `BigmaxrNonneg` containing the following lemmas:
    * `bigmaxr_mkcond`, `bigmaxr_split`, `bigmaxr_idl`, `bigmaxrID`,
      `bigmaxr_seq1`, `bigmaxr_pred1_eq`, `bigmaxr_pred1`, `bigmaxrD1`,
      `ler_bigmaxr_cond`, `ler_bigmaxr`, `bigmaxr_lerP`, `bigmaxr_sup`,
      `bigmaxr_ltrP`, `bigmaxr_gerP`, `bigmaxr_gtrP`
- in `sequences.v`:
  + lemma `closed_seq`
- in `normedtype.v`:
  + lemma `is_intervalPle`
- in `topology.v`:
  + lemma `continuous_cst`
  + definition `cvg_to_locally`
- in `csum.v`:
  + lemma `ub_ereal_sup_adherent_img`

## [0.3.10] - 2021-08-11

### Added

- in `classical_sets.v`:
  + lemmas `bigcup_image`, `bigcup_of_set1`
  + lemmas `bigcupD1`, `bigcapD1`
- in `boolp.v`:
  + definitions `equality_mixin_of_Type`, `choice_of_Type`
- in `normedtype.v`:
  + lemma `cvg_bounded_real`
  + lemma `pseudoMetricNormedZModType_hausdorff`
- in `sequences.v`:
  + lemmas `seriesN`, `seriesD`, `seriesZ`, `is_cvg_seriesN`, `lim_seriesN`,
    `is_cvg_seriesZ`, `lim_seriesZ`, `is_cvg_seriesD`, `lim_seriesD`,
    `is_cvg_seriesB`, `lim_seriesB`, `lim_series_le`, `lim_series_norm`
- in `measure.v`:
  + HB.mixin `AlgebraOfSets_from_RingOfSets`
  + HB.structure `AlgebraOfSets` and notation `algebraOfSetsType`
  + HB.instance `T_isAlgebraOfSets` in HB.builders `isAlgebraOfSets`
  + lemma `bigcup_set_cond`
  + definition `measurable_fun`
  + lemma `adde_undef_nneg_series`
  + lemma `adde_def_nneg_series`
  + lemmas `cvg_geometric_series_half`, `epsilon_trick`
  + definition `measurable_cover`
  + lemmas `cover_measurable`, `cover_subset`
  + definition `mu_ext`
  + lemmas `le_mu_ext`, `mu_ext_ge0`, `mu_ext0`, `measurable_uncurry`,
    `mu_ext_sigma_subadditive`
  + canonical `outer_measure_of_measure`

### Changed

- in `ereal.v`, definition `adde_undef` changed to `adde_def`
  + consequently, the following lemmas changed:
    * in `ereal.v`, `adde_undefC` renamed to `adde_defC`,
      `fin_num_adde_undef` renamed to `fin_num_adde_def`
    * in `sequences.v`, `ereal_cvgD` and `ereal_limD` now use hypotheses with `adde_def`
- in `sequences.v`:
  + generalize `{in,de}creasing_seqP`, `non{in,de}creasing_seqP` from `numDomainType`
    to `porderType`
- in `normedtype.v`:
  + generalized from `normedModType` to `pseudoMetricNormedZmodType`:
    * `nbhs_le_nbhs_norm`
    * `nbhs_norm_le_nbhs`
    * `nbhs_nbhs_norm`
    * `nbhs_normP`
    * `filter_from_norm_nbhs`
    * `nbhs_normE`
    * `filter_from_normE`
    * `near_nbhs_norm`
    * `nbhs_norm_ball_norm`
    * `nbhs_ball_norm`
    * `ball_norm_dec`
    * `ball_norm_sym`
    * `ball_norm_le`
    * `cvg_distP`
    * `cvg_dist`
    * `nbhs_norm_ball`
    * `dominated_by`
    * `strictly_dominated_by`
    * `sub_dominatedl`
    * `sub_dominatedr`
    * `dominated_by1`
    * `strictly_dominated_by1`
    * `ex_dom_bound`
    * `ex_strict_dom_bound`
    * `bounded_near`
    * `boundedE`
    * `sub_boundedr`
    * `sub_boundedl`
    * `ex_bound`
    * `ex_strict_bound`
    * `ex_strict_bound_gt0`
    * `norm_hausdorff`
    * `norm_closeE`
    * `norm_close_eq`
    * `norm_cvg_unique`
    * `norm_cvg_eq`
    * `norm_lim_id`
    * `norm_cvg_lim`
    * `norm_lim_near_cst`
    * `norm_lim_cst`
    * `norm_cvgi_unique`
    * `norm_cvgi_map_lim`
    * `distm_lt_split`
    * `distm_lt_splitr`
    * `distm_lt_splitl`
    * `normm_leW`
    * `normm_lt_split`
    * `cvg_distW`
    * `continuous_cvg_dist`
    * `add_continuous`
- in `measure.v`:
  + generalize lemma `eq_bigcupB_of`
  + HB.mixin `Measurable_from_ringOfSets` changed to `Measurable_from_algebraOfSets`
  + HB.instance `T_isRingOfSets` becomes `T_isAlgebraOfSets` in HB.builders `isMeasurable`
  + lemma `measurableC` now applies to `algebraOfSetsType` instead of `measureableType`
- moved from `normedtype.v` to `reals.v`:
  + lemmas `inf_lb_strict`, `sup_ub_strict`
- moved from `sequences.v` to `reals.v`:
  + lemma `has_ub_image_norm`

### Renamed

- in `classical_sets.v`:
  + `bigcup_mkset` -> `bigcup_set`
  + `bigsetU` -> `bigcup`
  + `bigsetI` -> `bigcap`
  + `trivIset_bigUI` -> `trivIset_bigsetUI`
- in `measure.v`:
  + `isRingOfSets` -> `isAlgebraOfSets`
  + `B_of` -> `seqD`
  + `trivIset_B_of` -> `trivIset_seqD`
  + `UB_of` -> `setU_seqD`
  + `bigUB_of` -> `bigsetU_seqD`
  + `eq_bigsetUB_of` -> `eq_bigsetU_seqD`
  + `eq_bigcupB_of` -> `eq_bigcup_seqD`
  + `eq_bigcupB_of_bigsetU` -> `eq_bigcup_seqD_bigsetU`

### Removed

- in `nngnum.v`:
  + lemma `filter_andb`

## [0.3.9] - 2021-06-12

### Added

- in `sequences.v`:
  + lemma `dvg_harmonic`
- in `classical_sets.v`:
  + definitions `image`, `image2`

### Changed

- in `classical_sets.v`
  + notations `[set E | x in A]` and `[set E | x in A & y in B]`
    now use definitions `image` and `image2` resp.
  + notation ``f @` A`` now uses the definition `image`
  + the order of arguments of `image` has changed compared to version 0.3.7:
    it is now `image A f` (it used to be `image f A`)

### Removed

- in `sequences.v`:
  + lemma `iter_addr`

## [0.3.8] - 2021-06-01

### Added

- file `reals.v`:
  + lemmas `le_floor`, `le_ceil`
- in `ereal.v`:
  + lemmas `big_nat_widenl`, `big_geq_mkord`
  + lemmas `lee_sum_nneg_natr`, `lee_sum_nneg_natl`
  + lemmas `ereal_sup_gt`, `ereal_inf_lt`
  + notation `0`/`1` for `0%R%:E`/`1%R:%E` in `ereal_scope`
- in `classical_sets.v`
  + lemma `subset_bigsetU_cond`
  + lemma `eq_imagel`
- in `sequences.v`:
  + notations `\sum_(i <oo) F i`
  + lemmas `ereal_pseries_sum_nat`, `lte_lim`
  + lemmas `is_cvg_ereal_nneg_natsum_cond`, `is_cvg_ereal_nneg_natsum`
  + lemma `ereal_pseriesD`, `ereal_pseries0`, `eq_ereal_pseries`
  + lemmas `leq_fact`, `prod_rev`, `fact_split`
  + definition `exp_coeff`
  + lemmas `exp_coeff_ge0`, `series_exp_coeff0`, `is_cvg_series_exp_coeff_pos`,
    ` normed_series_exp_coeff`, `is_cvg_series_exp_coeff `, `cvg_exp_coeff`
  + definition `expR`
- in `measure.v`:
  + lemma `eq_bigcupB_of_bigsetU`
  + definitions `caratheodory_type`
  + definition `caratheodory_measure` and lemma `caratheodory_measure_complete`
  + internal definitions and lemmas that may be deprecated and hidden in the future:
    * `caratheodory_measurable`, notation `... .-measurable`,
    * `le_caratheodory_measurable`, `outer_measure_bigcup_lim`,
      `caratheodory_measurable_{set0,setC,setU_le,setU,bigsetU,setI,setD}`
      `disjoint_caratheodoryIU`, `caratheodory_additive`,
          `caratheodory_lim_lee`, `caratheodory_measurable_trivIset_bigcup`,
      `caratheodory_measurable_bigcup`
  + definition `measure_is_complete`
- file `csum.v`:
  + lemmas `ereal_pseries_pred0`, `ub_ereal_sup_adherent_img`
  + definition `fsets`, lemmas `fsets_set0`, `fsets_self`, `fsetsP`, `fsets_img`
  + definition `fsets_ord`, lemmas `fsets_ord_nat`, `fsets_ord_subset`
  + definition `csum`, lemmas `csum0`, `csumE`, `csum_ge0`, `csum_fset`
    `csum_image`, `ereal_pseries_csum`, `csum_bigcup`
  + notation `\csum_(i in S) a i`
- file `cardinality.v`
  + lemmas `in_inj_comp`, `enum0`, `enum_recr`, `eq_set0_nil`, `eq_set0_fset0`,
    `image_nat_maximum`, `fset_nat_maximum`
  + defintion `surjective`, lemmas `surjective_id`, `surjective_set0`,
    `surjective_image`, `surjective_image_eq0`, `surjective_comp`
  + definition `set_bijective`,
  + lemmas `inj_of_bij`, `sur_of_bij`, `set_bijective1`, `set_bijective_image`,
    `set_bijective_subset`, `set_bijective_comp`
  + definition `inverse`
  + lemmas `injective_left_inverse`, `injective_right_inverse`,
    `surjective_right_inverse`,
  + notation `` `I_n ``
  + lemmas `II0`, `II1`, `IIn_eq0`, `II_recr`
  + lemmas `set_bijective_D1`, `pigeonhole`, `Cantor_Bernstein`
  + definition `card_le`, notation `_ #<= _`
  + lemmas `card_le_surj`, `surj_card_le`, `card_lexx`, `card_le0x`,
    `card_le_trans`, `card_le0P`, `card_le_II`
  + definition `card_eq`, notation `_ #= _`
  + lemmas `card_eq_sym`, `card_eq_trans`, `card_eq00`, `card_eqP`, `card_eqTT`,
    `card_eq_II`, `card_eq_le`, `card_eq_ge`, `card_leP`
  + lemma `set_bijective_inverse`
  + definition `countable`
  + lemmas `countable0`, `countable_injective`, `countable_trans`
  + definition `set_finite`
  + lemmas `set_finiteP`, `set_finite_seq`, `set_finite_countable`, `set_finite0`
  + lemma `set_finite_bijective`
  + lemmas `subset_set_finite`, `subset_card_le`
  + lemmas `injective_set_finite`, `injective_card_le`, `set_finite_preimage`
  + lemmas `surjective_set_finite`, `surjective_card_le`
  + lemmas `set_finite_diff`, `card_le_diff`
  + lemmas `set_finite_inter_set0_union`, `set_finite_inter`
  + lemmas `ex_in_D`, definitions `min_of_D`, `min_of_D_seq`, `infsub_enum`, lemmas
    `min_of_D_seqE`, `increasing_infsub_enum`, `sorted_infsub_enum`,
   `injective_infsub_enum`, `subset_infsub_enum`, `infinite_nat_subset_countable`
  + definition `enumeration`, lemmas `enumeration_id`, `enumeration_set0`.
  + lemma `ex_enum_notin`, definitions `min_of`, `minf_of_e_seq`, `smallest_of`
  + definition `enum_wo_rep`, lemmas `enum_wo_repE`, `min_of_e_seqE`,
    `smallest_of_e_notin_enum_wo_rep`, `injective_enum_wo_rep`, `surjective_enum_wo_rep`,
    `set_bijective_enum_wo_rep`, `enumration_enum_wo_rep`, `countable_enumeration`
  + lemmas `infinite_nat`, `infinite_prod_nat`, `countable_prod_nat`,
    `countably_infinite_prod_nat`

### Changed

- in `classical_sets.v`
  + lemma `subset_bigsetU`
  + notation ``f @` A`` defined as `[set f x | x in A]` instead of using `image`
- in `ereal.v`:
  + change implicits of lemma `lee_sum_nneg_ord`
  + `ereal_sup_ninfty` and `ereal_inf_pinfty` made equivalences
  + change the notation `{ereal R}` to `\bar R` and attach it to the scope `ereal_scope`
  + argument of `%:E` in `%R` by default
  + `F` argument of `\sum` in `%E` by default
- in `topology.v`:
  + change implicits of lemma `cvg_app`
- in `normedtype.v`:
  + `coord_continuous` generalized
- in `sequences.v`:
  + change implicits of lemma `is_cvg_ereal_nneg_series`
  + statements changed from using sum of ordinals to sum of nats
    * definition `series`
    * lemmas `ereal_nondecreasing_series`, `ereal_nneg_series_lim_ge`
    * lemmas `is_cvg_ereal_nneg_series_cond`, `is_cvg_ereal_nneg_series`
    * lemmas `ereal_nneg_series_lim_ge0`, `ereal_nneg_series_pinfty`

### Renamed

- in `ereal.v`:
  + `er` -> `extended`
  + `ERFin` -> `EFin`
  + `ERPInf` -> `EPInf`
  + `ERNInf` -> `ENInf`
  + `real_of_er` -> `real_of_extended`
  + `real_of_erD` -> `real_of_extendedD`
  + `ERFin_real_of_er` -> `EFin_real_of_extended`
  + `real_of_er_expand` -> `real_of_extended_expand`
  + `NERFin` -> `NEFin`
  + `addERFin` -> `addEFin`
  + `sumERFin`-> `sumEFin`
  + `subERFin` -> `subEFin`
- in `reals.v`:
  + `ler_ceil` -> `ceil_ge`
  + `Rceil_le` -> `le_Rceil`
  + `le_Rceil` -> `Rceil_ge`
  + `ge_Rfloor` -> `Rfloor_le`
  + `ler_floor` -> `floor_le`
  + `Rfloor_le` -> `le_Rfloor`
- in `topology.v`:
  + lemmas `onT_can` -> `onS_can`,
    `onT_can_in` -> `onS_can_in`,
    `in_onT_can` -> ``in_onS_can`
    (now in MathComp)
- in `sequences,v`:
  + `is_cvg_ereal_nneg_series_cond`
- in `forms.v`:
  + `symmetric` -> `symmetric_form`

### Removed

- in `classical_sets.v`
  + lemmas `eq_set_inl`, `set_in_in`
  + definition `image`
- from `topology.v`:
  + lemmas `homoRL_in`, `homoLR_in`, `homo_mono_in`, `monoLR_in`,
    `monoRL_in`, `can_mono_in`, `onW_can`, `onW_can_in`, `in_onW_can`,
    `onT_can`, `onT_can_in`, `in_onT_can` (now in MathComp)
- in `forms.v`:
  + lemma `mxdirect_delta`, `row_mx_eq0`, `col_mx_eq0`, `map_mx_comp`

## [0.3.7] - 2021-04-01

### Added

- in `topology.v`:
  + global instance `ball_filter`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pointedType`, `filteredType`, `topologicalType`,
      `uniformType`, `pseudoMetricType`
  + module `numFieldTopology` with an `Exports` submodule
    * many canonicals and coercions
  + global instance `Proper_nbhs'_regular_numFieldType`
  + definition `dense` and lemma `denseNE`
- in `normedtype.v`:
  + definitions `ball_`, `pointed_of_zmodule`, `filtered_of_normedZmod`
  + lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`
  + definition `pseudoMetric_of_normedDomain`
  + lemma `nbhs_ball_normE`
  + global instances `Proper_nbhs'_numFieldType`, `Proper_nbhs'_realType`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pseudoMetricNormedZmodType`, `normedModType`.
  + module `numFieldNormedType` with an `Exports` submodule
    * many canonicals and coercions
    * exports `Export numFieldTopology.Exports`
  + canonical `R_regular_completeType`, `R_regular_CompleteNormedModule`
- in `reals.v`:
  + lemmas `Rfloor_lt0`, `floor_lt0`, `ler_floor`, `ceil_gt0`, `ler_ceil`
  + lemmas `has_sup1`, `has_inf1`
- in `ereal.v`:
  + lemmas `ereal_ballN`, `le_ereal_ball`, `ereal_ball_ninfty_oversize`,
    `contract_ereal_ball_pinfty`, `expand_ereal_ball_pinfty`,
    `contract_ereal_ball_fin_le`, `contract_ereal_ball_fin_lt`,
    `expand_ereal_ball_fin_lt`, `ball_ereal_ball_fin_lt`, `ball_ereal_ball_fin_le`,
    `sumERFin`, `ereal_inf1`, `eqe_oppP`, `eqe_oppLRP`, `oppe_subset`,
    `ereal_inf_pinfty`
  + definition `er_map`
  + definition `er_map`
  + lemmas `adde_undefC`, `real_of_erD`, `fin_num_add_undef`, `addeK`,
    `subeK`, `subee`, `sube_le0`, `lee_sub`
  + lemmas `addeACA`, `muleC`, `mule1`, `mul1e`, `abseN`
  + enable notation `x \is a fin_num`
    * definition `fin_num`, fact `fin_num_key`, lemmas `fin_numE`, `fin_numP`
- in `classical_sets.v`:
  + notation `[disjoint ... & ..]`
  + lemmas `mkset_nil`, `bigcup_mkset`, `bigcup_nonempty`, `bigcup0`, `bigcup0P`,
    `subset_bigcup_r`, `eqbigcup_r`, `eq_set_inl`, `set_in_in`
- in `nngnum.v`:
  + instance `invr_nngnum`
- in `posnum.v`:
  + instance `posnum_nngnum`

## Changed

- in `ereal.v`:
  + generalize lemma `lee_sum_nneg_subfset`
  + lemmas `nbhs_oo_up_e1`, `nbhs_oo_down_e1`, `nbhs_oo_up_1e`, `nbhs_oo_down_1e`
    `nbhs_fin_out_above`, `nbhs_fin_out_below`, `nbhs_fin_out_above_below`
    `nbhs_fin_inbound`
- in `sequences.v`:
  + generalize lemmas `ereal_nondecreasing_series`, `is_cvg_ereal_nneg_series`,
    `ereal_nneg_series_lim_ge0`, `ereal_nneg_series_pinfty`
- in `measure.v`:
  + generalize lemma `bigUB_of`
  + generalize theorem `Boole_inequality`
- in `classical_sets.v`:
  + change the order of arguments of `subset_trans`

- canonicals and coercions have been changed so that there is not need
  anymore for explicit types casts to `R^o`, `[filteredType R^o of R^o]`,
  `[filteredType R^o * R^o of R^o * R^o]`, `[lmodType R of R^o]`,
  `[normedModType R of R^o]`,`[topologicalType of R^o]`, `[pseudoMetricType R of R^o]`
- `sequences.v` now imports `numFieldNormedType.Exports`
- `topology.v` now imports `reals`
- `normedtype.v` now imports `vector`, `fieldext`, `falgebra`,
  `numFieldTopology.Exports`
- `derive.v` now imports `numFieldNormedType.Exports`

### Renamed

- in `ereal.v`:
  + `is_realN` -> `fin_numN`
  + `is_realD` -> `fin_numD`
  + `ereal_sup_set0` -> `ereal_sup0`
  + `ereal_sup_set1` -> `ereal_sup1`
  + `ereal_inf_set0` -> `ereal_inf0`

### Removed

- in `topology.v`:
  + section `numFieldType_canonical`
- in `normedtype.v`:
  + lemma `R_ball`
  + definition `numFieldType_pseudoMetricNormedZmodMixin`
  + canonical `numFieldType_pseudoMetricNormedZmodType`
  + global instance `Proper_nbhs'_realType`
  + lemma `R_normZ`
  + definition `numFieldType_NormedModMixin`
  + canonical `numFieldType_normedModType`
- in `ereal.v`:
  + definition `is_real`

## [0.3.6] - 2021-03-04

### Added

- in `boolp.v`:
  + lemmas `iff_notr`, `iff_not2`
- in `classical_sets.v`:
  + lemmas `subset_has_lbound`, `subset_has_ubound`
  + lemma `mksetE`
  + definitions `cover`, `partition`, `pblock_index`, `pblock`
  + lemmas `trivIsetP`, `trivIset_sets`, `trivIset_restr`, `perm_eq_trivIset`
  + lemma `fdisjoint_cset`
  + lemmas `setDT`, `set0D`, `setD0`
  + lemmas `setC_bigcup`, `setC_bigcap`
- in `reals.v`:
  + lemmas `sup_setU`, `inf_setU`
  + lemmas `RtointN`, `floor_le0`
  + definition `Rceil`, lemmas `isint_Rceil`, `Rceil0`, `le_Rceil`, `Rceil_le`, `Rceil_ge0`
  + definition `ceil`, lemmas `RceilE`, `ceil_ge0`, `ceil_le0`
- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`, `esum_pinfty`
- in `normedtype.v`:
  + lemmas `ereal_nbhs'_le`, `ereal_nbhs'_le_finite`
  + lemmas `ball_open`
  + definition `closed_ball_`, lemmas `closed_closed_ball_`
  + definition `closed_ball`, lemmas `closed_ballxx`, `closed_ballE`,
    `closed_ball_closed`, `closed_ball_subset`, `nbhs_closedballP`, `subset_closed_ball`
  + lemmas `nbhs0_lt`, `nbhs'0_lt`, `interior_closed_ballE`, open_nbhs_closed_ball`
  + section "LinearContinuousBounded"
    * lemmas `linear_boundedP`, `linear_continuous0`, `linear_bounded0`,
      `continuousfor0_continuous`, `linear_bounded_continuous`, `bounded_funP`
- in `measure.v`:
  + definition `sigma_finite`

### Changed

- in `classical_sets.v`:
  + generalization and change of `trivIset` (and thus lemmas `trivIset_bigUI` and `trivIset_setI`)
  + `bigcup_distrr`, `bigcup_distrl` generalized
- header in `normedtype.v`, precisions on `bounded_fun`
- in `reals.v`:
  + `floor_ge0` generalized and renamed to `floorR_ge_int`
- in `ereal.v`, `ereal_scope` notation scope:
  + `x <= y` notation changed to `lee (x : er _) (y : er _)` and
    `only printing` notation `x <= y` for `lee x y`
  + same change for `<`
  + change extended to notations `_ <= _ <= _`, `_ < _ <= _`, `_ <= _ < _`, `_ < _ < _`

### Renamed

- in `reals.v`:
  + `floor` -> `Rfloor`
  + `isint_floor` -> `isint_Rfloor`
  + `floorE` -> `RfloorE`
  + `mem_rg1_floor` -> `mem_rg1_Rfloor`
  + `floor_ler` -> `Rfloor_ler`
  + `floorS_gtr` -> `RfloorS_gtr`
  + `floor_natz` -> `Rfloor_natz`
  + `Rfloor` -> `Rfloor0`
  + `floor1` -> `Rfloor1`
  + `ler_floor` -> `ler_Rfloor`
  + `floor_le0` -> `Rfloor_le0`
  + `ifloor` -> `floor`
  + `ifloor_ge0` -> `floor_ge0`
- in `topology.v`:
  + `ball_ler` -> `le_ball`
- in `normedtype.v`, `bounded_on` -> `bounded_near`
- in `measure.v`:
  + `AdditiveMeasure.Measure` -> `AdditiveMeasure.Axioms`
  + `OuterMeasure.OuterMeasure` -> `OuterMeasure.Axioms`

### Removed
- in `topology.v`:
  + `ball_le`
- in `classical_sets.v`:
  + lemma `bigcapCU`
- in `sequences.v`:
  + lemmas `ler_sum_nat`, `sumr_const_nat`

## [0.3.5] - 2020-12-21

### Added

- in `classical_sets.v`:
  + lemmas `predeqP`, `seteqP`

### Changed

- Requires:
  + MathComp >= 1.12
- in `boolp.v`:
  + lemmas `contra_not`, `contra_notT`, `contra_notN`, `contra_not_neq`, `contraPnot`
    are now provided by MathComp 1.12
- in `normedtype.v`:
  + lemmas `ltr_distW`, `ler_distW` are now provided by MathComp 1.12 as lemmas
    `ltr_distlC_subl` and `ler_distl_subl`
  + lemmas `maxr_real` and `bigmaxr_real` are now provided by MathComp 1.12 as
    lemmas `max_real` and `bigmax_real`
  + definitions `isBOpen` and `isBClosed` are replaced by the definition `bound_side`
  + definition `Rhull` now uses `BSide` instead of `BOpen_if`

### Removed

- Drop support for MathComp 1.11
- in `topology.v`:
  + `Typeclasses Opaque fmap.`

## [0.3.4] - 2020-12-12

### Added

- in `classical_sets.v`:
  + lemma `bigcup_distrl`
  + definition `trivIset`
  + lemmas `trivIset_bigUI`, `trivIset_setI`
- in `ereal.v`:
  + definition `mule` and its notation `*` (scope `ereal_scope`)
  + definition `abse` and its notation `` `| | `` (scope `ereal_scope`)
- in `normedtype.v`:
  + lemmas `closure_sup`, `near_infty_natSinv_lt`, `limit_pointP`
  + lemmas `closure_gt`, `closure_lt`
  + definition `is_interval`, `is_intervalPle`, `interval_is_interval`
  + lemma `connected_intervalP`
  + lemmas `interval_open` and `interval_closed`
  + lemmas `inf_lb_strict`, `sup_ub_strict`, `interval_unbounded_setT`,
    `right_bounded_interior`, `interval_left_unbounded_interior`, `left_bounded_interior`,
    `interval_right_unbounded_interior`, `interval_bounded_interior`
  + definition `Rhull`
  + lemma `sub_Rhull`, `is_intervalP`
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`
  + definitions `isSemiRingOfSets`, `SemiRingOfSets`, notation `semiRingOfSetsType`
  + definitions `RingOfSets_from_semiRingOfSets`, `RingOfSets`, notation `ringOfSetsType`
  + factory: `isRingOfSets`
  + definitions `Measurable_from_ringOfSets`, `Measurable`
  + lemma `semiRingOfSets_measurable{I,D}`
  + definition `diff_fsets`, lemmas `semiRingOfSets_diff_fsetsE`, `semiRingOfSets_diff_fsets_disjoint`
  + definitions `isMeasurable`
  + factory: `isMeasurable`
  + lemma `bigsetU_measurable`, `measurable_bigcap`
  + definitions `semi_additive2`, `semi_additive`, `semi_sigma_additive`
  + lemmas `semi_additive2P`, `semi_additiveE`, `semi_additive2E`,
    `semi_sigma_additive_is_additive`, `semi_sigma_additiveE`
  + `Module AdditiveMeasure`
     * notations `additive_measure`, `{additive_measure set T -> {ereal R}}`
  + lemmas `measure_semi_additive2`, `measure_semi_additive`, `measure_semi_sigma_additive`
  + lemma `semi_sigma_additive_is_additive`, canonical/coercion `measure_additive_measure`
  + lemma `sigma_additive_is_additive`
  + notations `ringOfSetsType`, `outer_measure`
  + definition `negligible` and its notation `.-negligible`
  + lemmas `negligibleP`, `negligible_set0`
  + definition `almost_everywhere` and its notation `{ae mu, P}`
  + lemma `satisfied_almost_everywhere`
  + definition `sigma_subadditive`
  + `Module OuterMeasure`
    * notation `outer_measure`, `{outer_measure set T -> {ereal R}}`
  + lemmas `outer_measure0`, `outer_measure_ge0`, `le_outer_measure`,
    `outer_measure_sigma_subadditive`, `le_outer_measureIC`
- in `boolp.v`:
  + lemmas `and3_asboolP`, `or3_asboolP`, `not_and3P`
- in `classical_sets.v`:
  + lemma `bigcup_sup`
- in `topology.v`:
  + lemmas `closure0`, `separatedC`, `separated_disjoint`, `connectedP`, `connected_subset`,
    `bigcup_connected`
  + definition `connected_component`
  + lemma `component_connected`

### Changed

- in `ereal.v`:
  + notation `x >= y` defined as `y <= x` (only parsing) instead of `gee`
  + notation `x > y` defined as `y < x` (only parsing) instead of `gte`
  + definition `mkset`
  + lemma `eq_set`
- in `classical_sets.v`:
  + notation `[set x : T | P]` now use definition `mkset`
- in `reals.v`:
  + lemmas generalized from `realType` to `numDomainType`:
    `setNK`, `memNE`, `lb_ubN`, `ub_lbN`, `nonemptyN`, `has_lb_ubN `
  + lemmas generalized from `realType` to `realDomainType`:
    `has_ubPn`, `has_lbPn`

## Renamed

- in `classical_sets.v`:
  + `subset_empty` -> `subset_nonempty`
- in `measure.v`:
  + `sigma_additive_implies_additive` -> `sigma_additive_is_additive`
- in `topology.v`:
  + `nbhs_of` -> `locally_of`
- in `topology.v`:
  + `connect0` -> `connected0`

## [0.3.3] - 2020-11-11

### Added

- in `boolp.v`:
  + lemma `not_andP`
  + lemma `not_exists2P`
- in `classical_sets.v`:
  + lemmas `setIIl`, `setIIr`, `setCS`, `setSD`, `setDS`, `setDSS`, `setCI`,
    `setDUr`, `setDUl`, `setIDA`, `setDD`
  + definition `dep_arrow_choiceType`
  + lemma `bigcup_set0`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`, `subsetEset`, `subEset`, `complEset`, `botEset`, `topEset`, `meetEset`, `joinEset`, `subsetPset`, `properPset`
  + Canonical `porderType`, `latticeType`, `distrLatticeType`, `blatticeType`, `tblatticeType`, `bDistrLatticeType`, `tbDistrLatticeType`, `cbDistrLatticeType`, `ctbDistrLatticeType`
  + lemmas `set0M`, `setM0`, `image_set0_set0`, `subset_set1`, `preimage_set0`
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
  + new lemmas: `lb_set1`, `ub_lb_set1`, `ub_lb_refl`, `lb_ub_lb`
  + new definitions and lemmas: `infimums`, `infimum`, `infimums_set1`, `is_subset1_infimum`
  + new lemmas: `ge_supremum_Nmem`, `le_infimum_Nmem`, `nat_supremums_neq0`
  + lemmas `setUCl`, `setDv`
  + lemmas `image_preimage_subset`, `image_subset`, `preimage_subset`
  + definition `proper` and its notation `<`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`, `subsetEset`, `subEset`, `complEset`, `botEset`, `topEset`, `meetEset`, `joinEset`, `properEneq`
  + Canonical `porderType`, `latticeType`, `distrLatticeType`, `blatticeType`, `tblatticeType`, `bDistrLatticeType`, `tbDistrLatticeType`, `cbDistrLatticeType`, `ctbDistrLatticeType` on classical `set`.
- file `nngnum.v`
- in `topology.v`:
  + definition `meets` and its notation `#`
  + lemmas `meetsC`, `meets_openr`, `meets_openl`, `meets_globallyl`,
    `meets_globallyr `, `meetsxx` and `proper_meetsxx`.
  + definition `limit_point`
  + lemmas `subset_limit_point`, `closure_limit_point`,
    `closure_subset`, `closureE`, `closureC`, `closure_id`
  + lemmas `cluster_nbhs`, `clusterEonbhs`, `closureEcluster`
  + definition `separated`
  + lemmas `connected0`, `connectedPn`, `connected_continuous_connected`
  + lemmas `closureEnbhs`, `closureEonbhs`, `limit_pointEnbhs`,
    `limit_pointEonbhs`, `closeEnbhs`, `closeEonbhs`.
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`
  + lemmas `gee0P`, `sume_ge0`, `lee_sum_nneg`, `lee_sum_nneg_ord`, `lee_sum_nneg_subset`, `lee_sum_nneg_subfset`
  + lemma `lee_addr`
  + lemma `lee_adde`
  + lemma `oppe_continuous`
  + lemmas `ereal_nbhs_pinfty_ge`, `ereal_nbhs_ninfty_le`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`, `geometric_invn`
  + lemmas `increasing_series`, `cvg_shiftS`, `mulrn_arithmetic`,
    `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`,
    `is_cvg_geometric_series`.
  + lemmas `ereal_cvgN`, `ereal_cvg_ge0`, `ereal_lim_ge`, `ereal_lim_le`
  + lemma `ereal_cvg_real`
  + lemmas `is_cvg_ereal_nneg_series_cond`, `is_cvg_ereal_nneg_series`, `ereal_nneg_series_lim_ge0`,
    `ereal_nneg_series_pinfty`
  + lemmas `ereal_cvgPpinfty`, `ereal_cvgPninfty`, `lee_lim`
  + lemma `ereal_cvgD`
    * with intermediate lemmas `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`, `ereal_cvgD_pinfty_pinfty`,
      `ereal_cvgD_ninfty_ninfty`
  + lemma `ereal_limD`
- in `normedtype.v`:
  + lemma `closed_ereal_le_ereal`
  + lemma `closed_ereal_ge_ereal`
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`

### Changed

- in `classical_sets.v`:
  + the index in `bigcup_set1` generalized from `nat` to some `Type`
  + lemma `bigcapCU` generalized
  + lemmas `preimage_setU` and `preimage_setI` are about the `setU` and `setI` (instead of `bigcup` and `bigcap`)
  + `eqEsubset` changed from an implication to an equality
- lemma `asboolb` moved from `discrete.v` to `boolp.v`
- lemma `exists2NP` moved from `discrete.v` to `boolp.v`
- lemma `neg_or` moved from `discrete.v` to `boolp.v` and renamed to `not_orP`
- definitions `dep_arrow_choiceClass` and `dep_arrow_pointedType`
  slightly generalized and moved from `topology.v` to
  `classical_sets.v`
- the types of the topological notions for `numFieldType` have been moved from `normedtype.v` to `topology.v`
- the topology of extended real numbers has been moved from `normedtype.v` to `ereal.v` (including the notions of filters)
- `numdFieldType_lalgType` in `normedtype.v` renamed to `numFieldType_lalgType` in `topology.v`
- in `ereal.v`:
  + the first argument of `real_of_er` is now maximal implicit
  + the first argument of `is_real` is now maximal implicit
  + generalization of `lee_sum`
- in `boolp.v`:
  + rename `exists2NP` to `forall2NP` and make it bidirectionnal
- moved the definition of `{nngnum _}` and the related bigmax theory to the new `nngnum.v` file

### Renamed

- in `classical_sets.v`:
  + `setIDl` -> `setIUl`
  + `setUDl` -> `setUIl`
  + `setUDr` -> `setUIr`
  + `setIDr` -> `setIUl`
  + `setCE` -> `setTD`
  + `preimage_setU` -> `preimage_bigcup`, `preimage_setI` -> `preimage_bigcap`
- in `boolp.v`:
  + `contrap` -> `contra_not`
  + `contrapL` -> `contraPnot`
  + `contrapR` -> `contra_notP`
  + `contrapLR` -> `contraPP`

### Removed

- in `boolp.v`:
  + `contrapNN`, `contrapTN`, `contrapNT`, `contrapTT`
  + `eqNN`
- in `normedtype.v`:
  + `forallN`
  + `eqNNP`
  + `existsN`
- in `discrete.v`:
  + `existsP`
  + `existsNP`
- in `topology.v`:
  + `close_to`
  + `close_cluster`, which is subsumed by `closeEnbhs`

## [0.3.2] - 2020-08-11

### Added

- in `boolp.v`, new lemma `andC`
- in `topology.v`:
  + new lemma `open_nbhsE`
  + `uniformType` a structure for uniform spaces based on entourages
    (`entourage`)
  + `uniformType` structure on products, matrices, function spaces
  + definitions `nbhs_`, `topologyOfEntourageMixin`, `split_ent`, `nbhsP`,
    `entourage_set`, `entourage_`, `uniformityOfBallMixin`, `nbhs_ball`
  + lemmas `nbhs_E`, `nbhs_entourageE`, `filter_from_entourageE`,
    `entourage_refl`, `entourage_filter`, `entourageT`, `entourage_inv`,
    `entourage_split_ex`, `split_entP`, `entourage_split_ent`,
    `subset_split_ent`, `entourage_split`, `nbhs_entourage`, `cvg_entourageP`,
    `cvg_entourage`, `cvg_app_entourageP`, `cvg_mx_entourageP`,
    `cvg_fct_entourageP`, `entourage_E`, `entourage_ballE`,
    `entourage_from_ballE`, `entourage_ball`, `entourage_proper_filter`,
    `open_nbhs_entourage`, `entourage_close`
  + `completePseudoMetricType` structure
  + `completePseudoMetricType` structure on matrices and function spaces
- in `classical_sets.v`:
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`, `adde_undef`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`, `addeAC`, `addeCA`
- in `normedtype.v`:
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`
  + lemmas `telescopeK`, `seriesK`, `increasing_series`, `cvg_shiftS`,
     `mulrn_arithmetic`, `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`, `is_cvg_geometric_series`.

### Changed

- moved from `normedtype.v` to `boolp.v` and renamed:
  + `forallN` -> `forallNE`
  + `existsN` -> `existsNE`
- `topology.v`:
  + `unif_continuous` uses `entourage`
  + `pseudoMetricType` inherits from `uniformType`
  + `generic_source_filter` and `set_filter_source` use entourages
  + `cauchy` is based on entourages and its former version is renamed
    `cauchy_ball`
  + `completeType` inherits from `uniformType` and not from `pseudoMetricType`
- moved from `posnum.v` to `Rbar.v`: notation `posreal`
- moved from `normedtype.v` to `Rstruct.v`:
  + definitions `R_pointedType`, `R_filteredType`, `R_topologicalType`,
    `R_uniformType`, `R_pseudoMetricType`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`, `continuity_ptE`,
    `continuity_pt_cvg'`, `continuity_pt_nbhs'`, `nbhs_pt_comp`
  + lemmas `close_trans`, `close_cvgxx`, `cvg_closeP` and `close_cluster` are
    valid for a `uniformType`
  + moved `continuous_withinNx` from `normedType.v` to `topology.v` and
    generalised it to `uniformType`
- moved from `measure.v` to `sequences.v`
  + `ereal_nondecreasing_series`
  + `ereal_nneg_series_lim_ge` (renamed from `series_nneg`)

### Renamed

- in `classical_sets.v`,
  + `ub` and `lb` are renamed to `ubound` and `lbound`
  + new lemmas:
    * `setUCr`, `setCE`, `bigcup_set1`, `bigcapCU`, `subset_bigsetU`
- in `boolp.v`,
  + `existsPN` -> `not_existsP`
  + `forallPN` -> `not_forallP`
  + `Nimply` -> `not_implyP`
- in `classical_sets.v`, `ub` and `lb` are renamed to `ubound` and `lbound`
- in `ereal.v`:
  + `eadd` -> `adde`, `eopp` -> `oppe`
- in `topology.v`:
  + `locally` -> `nbhs`
  + `locally_filterE` -> `nbhs_filterE`
  + `locally_nearE` -> `nbhs_nearE`
  + `Module Export LocallyFilter` -> `Module Export NbhsFilter`
  + `locally_simpl` -> `nbhs_simpl`
    * three occurrences
  + `near_locally` -> `near_nbhs`
  + `Module Export NearLocally` -> `Module Export NearNbhs`
  + `locally_filter_onE` -> `nbhs_filter_onE`
  + `filter_locallyT` -> `filter_nbhsT`
  + `Global Instance locally_filter` -> `Global Instance nbhs_filter`
  + `Canonical locally_filter_on` -> `Canonical nbhs_filter_on`
  + `neigh` -> `open_nbhs`
  + `locallyE` -> `nbhsE`
  + `locally_singleton` -> `nbhs_singleton`
  + `locally_interior` -> `nbhs_interior`
  + `neighT` -> `open_nbhsT`
  + `neighI` -> `open_nbhsI`
  + `neigh_locally` -> `open_nbhs_nbhs`
  + `within_locallyW` -> `within_nbhsW`
  + `prod_loc_filter` -> `prod_nbhs_filter`
  + `prod_loc_singleton` -> `prod_nbhs_singleton`
  + `prod_loc_loc` -> `prod_nbhs_nbhs`
  + `mx_loc_filter` -> `mx_nbhs_filter`
  + `mx_loc_singleton` -> `mx_nbhs_singleton`
  + `mx_loc_loc` -> `mx_nbhs_nbhs`
  + `locally'` -> `nbhs'`
  + `locallyE'` -> `nbhsE'`
  + `Global Instance locally'_filter` -> `Global Instance nbhs'_filter`
  + `Canonical locally'_filter_on` -> `Canonical nbhs'_filter_on`
  + `locally_locally'` -> `nbhs_nbhs'`
  + `Global Instance within_locally_proper` -> `Global Instance within_nbhs_proper`
  + `locallyP` -> `nbhs_ballP`
  + `locally_ball` -> `nbhsx_ballx`
  + `neigh_ball` -> `open_nbhs_ball`
  + `mx_locally` -> `mx_nbhs`
  + `prod_locally` -> `prod_nbhs`
  + `Filtered.locally_op` -> `Filtered.nbhs_op`
  + `locally_of` -> `nbhs_of`
  + `open_of_locally` -> `open_of_nhbs`
  + `locally_of_open` -> `nbhs_of_open`
  + `locally_` -> `nbhs_ball`
  + lemma `locally_ballE` -> `nbhs_ballE`
  + `locallyW` -> `nearW`
  + `nearW` -> `near_skip_subproof`
  + `locally_infty_gt` -> `nbhs_infty_gt`
  + `locally_infty_ge` -> `nbhs_infty_ge`
  + `cauchy_entouragesP` -> `cauchy_ballP`
- in `normedtype.v`:
  + `locallyN` -> `nbhsN`
  + `locallyC` -> `nbhsC`
  + `locallyC_ball` -> `nbhsC_ball`
  + `locally_ex` -> `nbhs_ex`
  + `Global Instance Proper_locally'_numFieldType` -> `Global Instance Proper_nbhs'_numFieldType`
  + `Global Instance Proper_locally'_realType` -> `Global Instance Proper_nbhs'_realType`
  + `ereal_locally'` -> `ereal_nbhs'`
  + `ereal_locally` -> `ereal_nbhs`
  + `Global Instance ereal_locally'_filter` -> `Global Instance ereal_nbhs'_filter`
  + `Global Instance ereal_locally_filter` -> `Global Instance ereal_nbhs_filter`
  + `ereal_loc_singleton` -> `ereal_nbhs_singleton`
  + `ereal_loc_loc` -> `ereal_nbhs_nbhs`
  + `locallyNe` -> `nbhsNe`
  + `locallyNKe` -> `nbhsNKe`
  + `locally_oo_up_e1` -> `nbhs_oo_up_e1`
  + `locally_oo_down_e1` -> `nbhs_oo_down_e1`
  + `locally_oo_up_1e` -> `nbhs_oo_up_1e`
  + `locally_oo_down_1e` -> `nbhs_oo_down_1e`
  + `locally_fin_out_above` -> `nbhs_fin_out_above`
  + `locally_fin_out_below` -> `nbhs_fin_out_below`
  + `locally_fin_out_above_below` -> `nbhs_fin_out_above_below`
  + `locally_fin_inbound` -> `nbhs_fin_inbound`
  + `ereal_locallyE` -> `ereal_nbhsE`
  + `locally_le_locally_norm` -> `nbhs_le_locally_norm`
  + `locally_norm_le_locally` -> `locally_norm_le_nbhs`
  + `locally_locally_norm` -> `nbhs_locally_norm`
  + `filter_from_norm_locally` -> `filter_from_norm_nbhs`
  + `locally_ball_norm` -> `nbhs_ball_norm`
  + `locally_simpl` -> `nbhs_simpl`
  + `Global Instance filter_locally` -> `Global Instance filter_locally`
  + `locally_interval` -> `nbhs_interval`
  + `ereal_locally'_le` -> `ereal_nbhs'_le`
  + `ereal_locally'_le_finite` -> `ereal_nbhs'_le_finite`
  + `locally_image_ERFin` -> `nbhs_image_ERFin`
  + `locally_open_ereal_lt` -> `nbhs_open_ereal_lt`
  + `locally_open_ereal_gt` -> `nbhs_open_ereal_gt`
  + `locally_open_ereal_pinfty` -> `nbhs_open_ereal_pinfty`
  + `locally_open_ereal_ninfty` -> `nbhs_open_ereal_ninfty`
  + `continuity_pt_locally` -> `continuity_pt_nbhs`
  + `continuity_pt_locally'` -> `continuity_pt_nbhs'`
  + `nbhs_le_locally_norm` -> `nbhs_le_nbhs_norm`
  + `locally_norm_le_nbhs` -> `nbhs_norm_le_nbhs`
  + `nbhs_locally_norm` -> `nbhs_nbhs_norm`
  + `locally_normP` -> `nbhs_normP`
  + `locally_normE` -> `nbhs_normE`
  + `near_locally_norm` -> `near_nbhs_norm`
  + lemma `locally_norm_ball_norm` -> `nbhs_norm_ball_norm`
  + `locally_norm_ball` -> `nbhs_norm_ball`
  + `pinfty_locally` -> `pinfty_nbhs`
  + `ninfty_locally` -> `ninfty_nbhs`
  + lemma `locally_pinfty_gt` -> `nbhs_pinfty_gt`
  + lemma `locally_pinfty_ge` -> `nbhs_pinfty_ge`
  + lemma `locally_pinfty_gt_real` -> `nbhs_pinfty_gt_real`
  + lemma `locally_pinfty_ge_real` -> `nbhs_pinfty_ge_real`
  + `locally_minfty_lt` -> `nbhs_minfty_lt`
  + `locally_minfty_le` -> `nbhs_minfty_le`
  + `locally_minfty_lt_real` -> `nbhs_minfty_lt_real`
  + `locally_minfty_le_real` -> `nbhs_minfty_le_real`
  + `lt_ereal_locally` -> `lt_ereal_nbhs`
  + `locally_pt_comp` -> `nbhs_pt_comp`
- in `derive.v`:
  + `derivable_locally` -> `derivable_nbhs`
  + `derivable_locallyP` -> `derivable_nbhsP`
  + `derivable_locallyx` -> `derivable_nbhsx`
  + `derivable_locallyxP` -> `derivable_nbhsxP`
- in `sequences.v`,
  + `cvg_comp_subn` -> `cvg_centern`,
  + `cvg_comp_addn` -> `cvg_shiftn`,
  + `telescoping` -> `telescope`
  + `sderiv1_series` -> `seriesSB`
  + `telescopingS0` -> `eq_sum_telescope`

### Removed

- in `topology.v`:
  + definitions `entourages`, `topologyOfBallMixin`, `ball_set`
  + lemmas `locally_E`, `entourages_filter`, `cvg_cauchy_ex`

## [0.3.1] - 2020-06-11

### Added

- in `boolp.v`, lemmas for classical reasoning `existsNP`, `existsPN`,
  `forallNP`, `forallPN`, `Nimply`, `orC`.
- in `classical_sets.v`, definitions for supremums: `ul`, `lb`,
  `supremum`
- in `ereal.v`:
  + technical lemmas `lee_ninfty_eq`, `lee_pinfty_eq`, `lte_subl_addr`, `eqe_oppLR`
  + lemmas about supremum: `ereal_supremums_neq0`
  + definitions:
    * `ereal_sup`, `ereal_inf`
  + lemmas about `ereal_sup`:
    * `ereal_sup_ub`, `ub_ereal_sup`, `ub_ereal_sup_adherent`
- in `normedtype.v`:
  + function `contract` (bijection from `{ereal R}` to `R`)
  + function `expand` (that cancels `contract`)
  + `ereal_pseudoMetricType R`

### Changed

- in `reals.v`, `pred` replaced by `set` from `classical_sets.v`
  + change propagated in many files

## [0.3.0] - 2020-05-26

This release is compatible with MathComp version 1.11+beta1.

The biggest change of this release is compatibility with MathComp
1.11+beta1.  The latter introduces in particular ordered types.
All norms and absolute values have been unified, both in their denotation `|_| and in their theory.

### Added

- `sequences.v`: Main theorems about sequences and series, and examples
  + Definitions:
    * `[sequence E]_n` is a special notation for `fun n => E`
    * `series u_` is the sequence of partial sums
    * `[normed S]` is the series of absolute values, if S is a series
    * `harmonic` is the name of a sequence,
       apply `series` to them to get the series.
  + Theorems:
    * lots of helper lemmas to prove convergence of sequences
    * convergence of harmonic sequence
    * convergence of a series implies convergence of a sequence
    * absolute convergence implies convergence of series
- in `ereal.v`: lemmas about extended reals' arithmetic
- in `normedtype.v`: Definitions and lemmas about generic domination,
  boundedness, and lipschitz
  + See header for the notations and their localization
  + Added a bunch of combinators to extract existential witnesses
  + Added `filter_forall` (commutation between a filter and finite forall)
- about extended reals:
  + equip extended reals with a structure of topological space
  + show that extended reals are hausdorff
- in `topology.v`, predicate `close`
- lemmas about bigmaxr and argmaxr
  + `\big[max/x]_P F = F [arg max_P F]`
  + similar lemma for `bigmin`
- lemmas for `within`
- add `setICl` (intersection of set with its complement)
- `prodnormedzmodule.v`
  + `ProdNormedZmodule` transfered from MathComp
  + `nonneg` type for non-negative numbers
- `bigmaxr`/`bigminr` library
- Lemmas `interiorI`, `setCU` (complement of union is intersection of complements),
  `setICl`, `nonsubset`, `setC0`, `setCK`, `setCT`, `preimage_setI/U`, lemmas about `image`

### Changed

- in `Rstruct.v`, `bigmaxr` is now defined using `bigop`
- `inE` now supports `in_setE` and `in_fsetE`
- fix the definition of `le_ereal`, `lt_ereal`
- various generalizations to better use the hierarchy of `ssrnum` (`numDomainType`,
  `numFieldType`, `realDomainType`, etc. when possible) in `topology.v`,
  `normedtype.v`, `derive.v`, etc.

### Renamed

- renaming `flim` to `cvg`
  + `cvg` corresponds to `_ --> _`
  + `lim` corresponds to `lim _`
  + `continuous`  corresponds to continuity
  + some suffixes `_opp`, `_add` ... renamed to `N`, `D`, ...
- big refactoring about naming conventions
  + complete the theory of `cvg_`, `is_cvg_` and `lim_` in normedtype.v
    with consistent naming schemes
  + fixed differential of `inv` which was defined on `1 / x` instead of `x^-1`
  + two versions of lemmas on inverse exist
    * one in realType (`Rinv_` lemmas), for which we have differential
    * a general one `numFieldType`  (`inv_` lemmas in normedtype.v, no differential so far, just continuity)
  + renamed `cvg_norm` to `cvg_dist` to reuse the name `cvg_norm` for
    convergence under the norm
- `Uniform` renamed to `PseudoMetric`
- rename `is_prop` to `is_subset1`

### Removed

- `sub_trans` (replaced by MathComp's `subrKA`)
- `derive.v` does not require `Reals` anymore
- `Rbar.v` is almost not used anymore

### Infrastructure

- NIX support
  + see `config.nix`, `default.nix`
  + for the CI also

### Misc
