# Changelog (unreleased)

## [Unreleased]

### Added
- in order_topology.v
  + lemma `itv_closed_ends_closed`
- in classical_sets.v
  + lemma `in_set1_eq`

- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

- in `Rstruct.v`:
  + lemmas `R0E` and `R1E`
  + multirule `RealsE` to convert from Stdlib reals to Analysis ones

- in `Rstruct_topology.v`:
  + lemma `RlnE`
- in probability.v
  + lemma `pmf_ge0`
  + lemmas `pmf_gt0_countable`, `pmf_measurable`
- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

- in `set_interval.v`:
  + lemmas `itv_setU_setT`, `disjoint_rays`

- in `constructive_ereal.v`:
  + lemma `ltgte_fin_num`

- in `probability.v`:
  + definition `ccdf`
  + lemmas `lebesgue_stieltjes_cdf_id`, `cdf_ccdf_1`, `ccdf_nonincreasing`, `cvg_ccdfy0`, `cvg_ccdfNy1`, `ccdf_right_continuous`, `ge0_expectation_ccdf`
  + corollaries `ccdf_cdf_1`, `ccdf_1_cdf`, `cdf_1_ccdf`

- in `num_normedtype.v`:
  + lemma `nbhs_infty_gtr`
- in `function_spaces.v`:
  + lemmas `cvg_big`, `continuous_big`

- in `realfun.v`:
  + lemma `cvg_addrl_Ny`

- in `constructive_ereal.v`:
  + lemmas `mule_natr`, `dmule_natr`
  + lemmas `inve_eqy`, `inve_eqNy`

- in `uniform_structure.v`:
  + lemma `continuous_injective_withinNx`

- in `constructive_ereal.v`:
  + variants `Ione`, `Idummy_placeholder`
  + inductives `Inatmul`, `IEFin`
  + definition `parse`, `print`
  + number notations in scopes `ereal_dual_scope` and `ereal_scope`
  + notation `- 1` in scopes `ereal_dual_scope` and `ereal_scope`
- in `pseudometric_normed_Zmodule.v`:
  + lemma `le0_ball0`
- in `theories/landau.v`:
  + lemma `littleoE0`

- in `constructive_ereal.v`:
  + lemma `lt0_adde`

- in `unstable.v`
  + lemmas `coprime_prodr`, `Gauss_dvd_prod`, `expn_prod`, `mono_leq_infl`,
    `card_big_setU`

- file `pnt.v`
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

- in `realfun.v`:
  + lemmas `derivable_oy_continuous_within_itvcy`,
           `derivable_oy_continuous_within_itvNyc`
  + lemmas `derivable_oo_continuousW`,
           `derivable_oy_continuousWoo`,
           `derivable_oy_continuousW`,
           `derivable_Nyo_continuousWoo`,
           `derivable_Nyo_continuousW`

- in `realfun.v`:
  + lemma `derivable_oy_RcontinuousN`

- in `ftc.v`:
  + lemmas `integration_by_partsy_ge0_ge0`,
           `integration_by_partsy_le0_ge0`,
           `integration_by_partsy_le0_le0`,
           `integration_by_partsy_ge0_le0`

- in `real_interval.v`:
  + lemma `subset_itvoSo_cSc`

### Changed
- in set_interval.v
  + `itv_is_closed_unbounded` (fix the definition)

- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

- in `lebesgue_Rintegrable.v`:
  + lemma `Rintegral_cst` (does not use `cst` anymore)

- split `probability.v` into directory `probability_theory` and move contents as:
  + file `probability.v`:
  + file `bernoulli_distribution.v`:
    * definitions `bernoulli_pmf`, `bernoulli_prob`
    * lemmas `bernoulli_pmf_ge0`, `bernoulli_pmf1`, `measurable_bernoulli_pmf`,
      `eq_bernoulli`, `bernoulli_dirac`, `eq_bernoulliV2`, `bernoulli_probE`,
      `measurable_bernoulli_prob`, `measurable_bernoulli_prob2`
  + file `beta_distribution.v`:
    * lemmas `continuous_onemXn`, `onemXn_derivable`, `derivable_oo_LRcontinuous_onemXnMr`,
      `derive_onemXn`, `Rintegral_onemXn`
    * definition `XMonemX`
    * lemmas `XMonemX_ge0`, `XMonemX_le1`, `XMonemX0n`, `XMonemXn0`, `XMonemX00`,
      `XMonemXC`, XMonemXM`, `continuous_XMonemX`, `within_continuous_XMonemX`,
      `measurable_XMonemX`, `bounded_XMonemX`, `integrable_XMonemX`, `integrable_XMonemX_restrict`,
      `integral_XMonemX_restrict`
    * definition `beta_fun`
    * lemmas `EFin_beta_fun`, `beta_fun_sym`, `beta_fun0n`, `beta_fun00`, `beta_fun1Sn`,
      `beta_fun11`, `beta_funSSnSm`, `beta_funSnSm`, `beta_fun_fact`, `beta_funE`,
      `beta_fun_gt0`, `beta_fun_ge0`
    * definition `beta_pdf`
    * lemmas `measurable_beta_pdf`, `beta_pdf_ge0`, `beta_pdf_le_beta_funV`, `integrable_beta_pdf`,
      `bounded_beta_pdf_01`
    * definition `beta_prob`
    * lemmas integral_beta_pdf`, `beta_prob01`, `beta_prob_fin_num`, `beta_prob_dom`,
      `beta_prob_uniform`, `integral_beta_prob_bernoulli_prob_lty`,
      `integral_beta_prob_bernoulli_prob_onemX_lty`,
      `integral_beta_prob_bernoulli_prob_onem_lty`, `beta_prob_integrable`,
      `beta_prob_integrable_onem`, `beta_prob_integrable_dirac`,
      `beta_prob_integrable_onem_dirac`, `integral_beta_prob`
    * definition `div_beta_fun`
    * lemmas `div_beta_fun_ge0`, `div_beta_fun_le1`
    * definition `beta_prob_bernoulli_prob`
    * lemmas `beta_prob_bernoulli_probE`
  + file `binomial_distribution.v`:
    * definition `binomial_pmf`
    * lemmas `measurable_binomial_pmf`
    * definition `binomial_prob`
    * definition `bin_prob`
    * lemmas `bin_prob0`, `bin_prob1`, `binomial_msum`, `binomial_probE`,
      `integral_binomial`, `integral_binomial_prob`, `measurable_binomial_prob`
  + file `exponential_distribution.v`:
    * definition `exponential_pdf`
    * lemmas `exponential_pdf_ge0`, `lt0_exponential_pdf`, `measurable_exponential_pdf`,
      `exponential_pdfE`, `in_continuous_exponential_pdf`, `within_continuous_exponential_pdf`
    * definition `exponential_prob`
    * lemmas `derive1_exponential_pdf`, `exponential_prob_itv0c`, `integral_exponential_pdf`,
      `integrable_exponential_pdf`
  + file `normal_distribution.v`:
    * definition `normal_fun`
    * lemmas `measurable_normal_fun`, normal_fun_ge0`, `normal_fun_center`
    * definition `normal_peak`
    * lemmas `normal_peak_ge0`, `normal_peak_gt0`
    * definition `normal_pdf`
    * lemmas `normal_pdfE`, `measurable_normal_pdf`, `normal_pdf_ge0`, `continuous_normal_pdf`,
      `normal_pdf_ub`
    * definition `normal_prob`
    * lemmas `integral_normal_pdf`, `integrable_normal_pdf`, `normal_prob_dominates`
  + file `poisson_distribution.v`:
    * definition `poisson_pmf`
    * lemmas `poisson_pmf_ge0`, `measurable_poisson_pmf`
    * definition `poisson_prob`
    * lemma `measurable_poisson_prob`
  + file `uniform_distribution.v`:
    * definition `uniform_pdf`
    * lemmas `uniform_pdf_ge0`, `measurable_uniform_pdf`, `integral_uniform_pdf`,
      `integral_uniform_pdf1`
    * definition `uniform_prob`
    * lemmmas `integrable_uniform_pdf`, `dominates_uniform_prob`,
      `integral_uniform`
  + file `random_variable.v`:
    * definition `random_variable`
    * lemmas `notin_range_measure`, `probability_range`
    * definition `distribution`
    * lemmas `probability_distribution`, `ge0_integral_distribution`, `integral_distribution`
    * definition `cdf`
    * lemmas `cdf_ge0`, `cdf_le1`, `cdf_nondecreasing`, `cvg_cdfy1`, `cvg_cdfNy0`,
      `cdf_right_continuous`, `cdf_lebesgue_stieltjes_id`, `lebesgue_stieltjes_cdf_id`,
    * definition `ccdf`
    * lemmas `cdf_ccdf_1`
    * corollaries `ccdf_cdf_1`, `ccdf_1_cdf`, `cdf_1_ccdf`
    * lemmas `ccdf_nonincreasing`, `cvg_ccdfy0`, `cvg_ccdfNy1`, `ccdf_right_continuous`
    * definition `expectation`
    * lemmas `expectation_def`, `expectation_fin_num`, `expectation_cst`,
      `expectation_indic`, `integrable_expectation`, `expectationZl`,
      `expectation_ge0`, `expectation_le`, `expectationD`, `expectationB`,
      `expectation_sum`, `ge0_expectation_ccdf`
    * definition `covariance`
    * lemmas `covarianceE`, `covarianceC`, `covariance_fin_num`,
      `covariance_cst_l`, `covariance_cst_r`, `covarianceZl`, `covarianceZr`,
      `covarianceNl`, `covarianceNr`, `covarianceNN`, `covarianceDl`, `covarianceDr`,
      `covarianceBl`, `covarianceBr`
    * definition `variance`
    * lemmas `varianceE`, `variance_fin_num`, `variance_ge0`, `variance_cst`,
      `varianceZ`, `varianceN`, `varianceD`, `varianceB`, `varianceD_cst_l`, `varianceD_cst_r`,
      `varianceB_cst_l`, `varianceB_cst_r`, `covariance_le`
    * definition `mmt_gen_fun`
    * lemmas `markov`, `chernoff`, `chebyshev`, `cantelli`
    * definition `discrete_random_variable`
    * lemmas `dRV_dom_enum`
    * definitions `dRV_dom`, `dRV_enum`, `enum_prob`
    * lemmas `distribution_dRV_enum`, `distribution_dRV`, `sum_enum_prob`
    * definition `pmf`
    * lemmas `pmf_ge0`, `pmf_gt0_countable`, `pmf_measurable`, `dRV_expectation`,
      `expectation_pmf`
- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

- in `lebesgue_stieltjes_measure.v` specialized from `numFieldType` to `realFieldType`:
  + lemma `nondecreasing_right_continuousP` 
  + definition `CumulativeBounded`

- in `lebesgue_stieltjes_measure.v`, according to generalization of `Cumulative`, modified:
  + lemmas `wlength_ge0`, `cumulative_content_sub_fsum`, `wlength_sigma_subadditive`, `lebesgue_stieltjes_measure_unique`
  + definitions `lebesgue_stieltjes_measure`, `completed_lebesgue_stieltjes_measure`

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

- in `constructive_ereal.v`:
  + instance of `Monoid.isLaw` for `mine`

- in `probability.v`:
  + definition `poisson_pmf`, lemmas `poisson_pmf_ge0`, `measurable_poisson_pmf`,
  + definition `poisson_prob`

- in `measurable_function.v`:
  + lemma `measurable_funS`: implicits changed

### Renamed
- in `set_interval.v`:
  + lemmas `setU_itvob1`, `setU_1itvob`

- in `realfun.v`:
  + lemma `derivable_sqrt`
- in `classical_sets.v`:
  + definition `rectangle`
  + lemmas `rectangle_setX`, `setI_closed_rectangle`
  + definitions `cross`, `cross12`
  + lemmas `smallest_sub_sub`, `bigcap_closed_smallest`, `smallest_sub_iff`
  + lemma `preimage_set_systemS`
  + lemma `setD_bigcapr`

- in `measurable_structure.v`:
  + lemmas `g_sigma_algebra_cross`, `g_sigma_algebra_rectangle`
  + lemma `sigma_algebra_sub`

- in `measurable_function.v`:
  + lemma `preimage_measurability`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `itv_center_shift`

- in `normed_module.v`:
  + lemmas `closure_itvoo`
- in `unstable.v`:
  + structures `SemiNorm`, `Norm`
  + lemmas `normMn`, `normN`, `ler_norm_sum`

- in `normed_module.v`:
  + structure `NormedVector`
  + notation `normedVectType`
  + definition `max_space`
  + lemmas `sup_closed_ball_compact`, `equivalence_norms`,
    `linear_findim_continuous`

- in `tvs.v`:
  + lemmas `cvg_sum`, `sum_continuous`

- in `classical_sets.v`:
  + lemmas `setI_closed_setT`, `setI_closed_set0`

- in `measurable_function.v`:
  + lemma `g_sigma_algebra_preimage_comp`

- in `measure_function.v`:
  + lemma `g_sigma_algebra_finite_measure_unique`

- new file `independence.v`:
  + definition `independent_events`
  + definition `mutual_independence`
  + lemma `eq_mutual_independence`
  + definition `independence2`, `independence2P`
  + lemma `mutual_independence_fset`
  + lemma `mutual_independence_finiteS`
  + theorem `mutual_independence_finite_g_sigma`
  + lemma `mutual_dependence_bigcup`
  + definition `independent_RVs`
  + lemma `independent_RVsD1`
  + theorem `independent_generators`
  + definition `independent_RVs2`
  + lemmas `independent_RVs2_comp`, `independent_RVs2_funrposneg`,
    `independent_RVs2_funrnegpos`, `independent_RVs2_funrnegneg`,
    `independent_RVs2_funrpospos`
  + definition `pairRV`, lemma `measurable_pairRV`
  + lemmas `independent_RVs2_product_measure1`
  + lemmas `independent_RVs2_setI_preimage`,
    `independent_Lfun1_expectation_product_measure_lty`
  + lemma `ge0_independent_expectationM`
  + lemmas `independent_Lfun1_expectationM_lty`, `independent_Lfun1M`,
    `independent_expectationM`

- in `ereal.v`:
  + lemma `ge0_addBefctE`

- in `measure_extension.v`:
  + definition `caratheodory_measure`
- in `measurable_structure.v`:
  + structure `PMeasurable`, notation `pmeasurableType`

- in `subspace_topology.v`:
  + lemma `withinU_continuous_patch`
- in `matrix_normedtype.v`:
  + lemma `continuous_mx`

- in `derive.v`:
  + instance `is_derive_mx`
  + fact `dmx`
  + lemma `diffmx`
  + lemma `is_diff_mx`
  + instance `is_diff_mx`
- in `realsum.v`:
  + lemma `esum_psum`
  + lemma `esum_sum`

- in `constructive_ereal.v`:
  + definition `esg`
  + lemmas `numEesg`, `gte0_esg`, `lte0_esg`, `esg0`

- in `esum.v`:
  + lemmas `esum_eq0P`, `esumZ`, `exchange_esum`
  + lemmas `le_esum`, `esumN`
  + lemmas `summable_le_esum`, `summable_esum_funepos`, `summable_esumN`,
    `summableZ`, `summable_esumZ`
  + lemmas `esum_if_eq_op`
  + lemmas `exchange_esum_ereal_sup`

- in `ereal.v`:
  + lemmas `exchange_ereal_sup`, `ge0_ereal_supZl`, `ge0_ereal_supZl_range`

- in `sequences.v`:
  + lemmas `ereal_supD`, `ereal_sup_sum`

- in `reals.v`:
  + lemmas `sup_ge0`, `has_sup_wpZl`, `gt0_has_supZl`, `has_sup_Mn`, `sup_Mn`
- in `mathcomp_extra.v`:
  + lemmas `divDl_ge0`, `divDl_le1`

- in `unstable.v`:
  + lemmas `divD_onem`

- in `filter.v`:
  + mixin `isSubNbhs`, structure `SubNbhs`, notation `subNbhsType`

- in `topology_structure.v`:
  + structure `SubTopological`, notation `subTopologicalType`

- in `tvs.v`:
  + structure `SubConvexTvs`, notation `subConvexTvsType`

- in `normed_module.v`:
  + structure `SubNormedModule`, notation `subNormedModType`
  + instance `ent_xsection_filter`
  + light-weigth factory `subLmodule_isSubNormedmodule`

- new file `hahn_banach_theorem.v`:
  + module `LinearGraph`
    * definitions `graph`, `linear_graph`
    * lemmas `lingraph_00`, `lingraphZ`, `lingraphD`
  + module `HahnBanachZorn`
    * definitions `extend_graph`, `le_graph`, `functional_graph`, `le_extend_graph`
    * record `zorn_type`
    * definition `zphi`
    * lemma `zorn_type_eq`
    * definition `zornS`
    * lemmas `zornS_ex`, `domain_extend`, `hahn_banach_witness`
  + theorems `hahn_banach_extension`, `hahn_banach_extension_normed`
- in `normal_distribution.v`:
  + lemma `normal_funN`
  + lemma `normal_fun_sym`
  + lemma `normal_fun0abs`
  + lemma `normal_pdf_sym`
  + lemma `normal_fun_center_new`
  + lemma `normal_fun_shift`
  + lemma `normal_pdf_uniq_ae`
  + lemma `normal_prob_continuous`
  + lemma `integral_normal_prob`
  + lemma `measurable_normal_prob`
  + lemma `emeasurable_bounded_integrable`
  + lemmas `integrable_normal_probD1`, `normal_probD1`, `normal_probD2`, `normal_probD`

- in `lebesgue_stieltjes_measure.v`:
  + definition `lebesgue_display`

- in `realsum.v`:
  + lemma `esum_summableP`

- in `esum.v`:
  + lemma `fsetsTE`
- in `ftc.v`:
  + lemma `ge0_integration_by_substitution_shift_itvy`,
    `ge0_integration_by_substitution_shift_itvNy`
- in `derive.v`:
  + lemmas `derivable_row_mx`, `derive_row_mx`
  + instance `is_derive_row_mx`

- in `matrix_normedtype.v`
  + lemmas `norm_row_mx`, `norm_row_mx0r`, `norm_row_mx0l`, `cvg_row_mx`

- in `unstable.v`:
  + lemma `sub_row_mx`

- in `derive.v`:
  + lemmas `eqo_row_mx`, `drow_mx`, `diff_row_mx`,
    `differentiable_row_mx`
  + instance `is_diff_row_mx`

- in `functions.v`:
  + lemmas `zerofctE`, `onefctE`

- in `functions.v`:
  + lemmas `linfunP`, `linfun_eqP`
  + instances of `SubLmodule` and `pointedType` on `{linear _->_ | _ }`

- in `tvs.v`:
  + structure `LinearContinuous`
  + factory `isLinearContinuous`
  + instance of `ChoiceType` on `{linear_continuous _ -> _ }`
  + instance of `LinearContinuous` with the composition of two functions of type `LinearContinuous`
  + instance of `LinearContinuous` with the sum of two functions of type `LinearContinuous`
  + instance of `LinearContinuous` with the scalar multiplication of a function of type
    `LinearContinuous`
  + instance of `Continuous` on \-f when f is of type `LinearContinuous`
  + instance of `SubModClosed` on `{linear_continuous _ -> _}`
  + instance of `SubLModule` on  `{linear_continuous _ -> _ }`
  + instance of `LinearContinuous` on the null function
  + notations `{linear_continuous _ -> _ | _ }` and `{linear_continuous _ -> _ }`
  + definitions `lcfun`, `lcfun_key`, `lcfunP`
  + lemmas `lcfun_eqP`, `null_fun_continuous`, `fun_cvgD`,
   `fun_cvgN`, `fun_cvgZ`, `fun_cvgZr`
  + lemmas `lcfun_continuous` and `lcfun_linear`

- new files `signed_measure.v` and `radon_nikodym.v`
  + with the contents of `charge.v` (deprecated)

- in `esum.v`:
  + lemma `ge0_esum`
  + lemma `esum_ge`

- in `functions.v`:
  + lemma `preimageD1`

- in `measure_function.v`:
  + lemmas `cvg_measure_bigcap`, `cvg_measure_bigcup`

- in `classical_sets.v`:
  + lemma `bigcup_bigsetU`

- in `measurable_structure.v`:
  + lemmas `countable_bigcap_measurable`, `countable_bigcup_measurable`

### Changed

- in `realsum.v`:
  + lemma `__admitted__psumB` proved and renamed to `psumB`

- moved from `measurable_structure.v` to `classical_sets.v`:
  + definition `preimage_set_system`
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
    `preimage_set_system_id`
  
- moved from `measurable_structure.v` to `classical_sets.v`:
  + definition `preimage_set_system`
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
    `preimage_set_system_id`

- moved from `topology_structure.v` to `filter.v`:
  + lemma `continuous_comp` (and generalized)

- in `numfun.v`:
  + `fune_abse` renamed to `funeposDneg` and direction of the equality changed
  + `funeposneg` renamed to `funeposBneg` and direction of the equality changed
  + `funeD_posD` renamed to `funeDB` and direction of the equality changed

- in `constructive_ereal.v`:
  + lemmas `EFin_semi_additive` and `dEFin_semi_additive` turned into `Let`s

- moved from `charge.v` to `signed_measure.v`:
  + mixin `isAdditiveCharge`, structure `AdditiveCharge`
  + mixin `isSemiSigmaAdditive`, structure `Charge`
  + factory `isCharge`
  + lemmas `charge0`, `charge_semi_additiveW`, `charge_semi_additive2E`,
    `charge_semi_additive2`, `chargeU`, `chargeDI`, `charge_partition`
  + definitions `measure_of_charge`, `charge_of_finite_measure`
  + lemma `chargeD`
  + definitions `crestr`, `crestr0`, `czero`, `cscale`
  + lemmas `dominates_cscalel`, `dominates_cscaler`
  + definition `copp`
  + lemma `cscaleN1`
  + definition `cadd`
  + lemmas `dominates_cadd`, `dominates_pushforward`
  + definitions `positive_set`, `negative_set`
  + lemmas `negative_set_charge_le0`, `negative_set0`,
    `positive_negative0`, `bigcup_negative_set`, `negative_setU`,
    `hahn_decomposition_lemma`
  + definition `hahn_decomposition`
  + theorem `Hahn_decomposition`
  + lemmas `Hahn_decomposition_uniq`, `cjordan_posE`, `cjordan_negE`
  + definitions `jordan_pos`, `jordan_neg`
  + lemmas `jordan_posE`, `jordan_negE`, `jordan_decomp`, `jordan_pos_dominates`,
    `jordan_neg_dominates`
  + definition `charge_variation`, `charge_dominates`
  + lemmas `abse_charge_variation`, `null_charge_dominatesP`,
    `content_charge_dominatesP`, `charge_variation_continuous`

- moved from `charge.v` to `radon_nikodym.v`:
  + definition `induced_charge`
  + lemmas `semi_sigma_additive_nng_induced`, `dominates_induced`,
    `integral_normr_continuous`
  + definitions `approxRN`, `int_approxRN`, `sup_int_approxRN`
  + lemmas `sup_int_approxRN_ge0`, `radon_nikodym_finite`,
    `radon_nikodym_sigma_finite`, `change_of_variables`, `integrableM`,
    `chain_rule`
  + definition `Radon_Nikodym`
  + lemmas `Radon_NikodymE`, `Radon_Nikodym_fin_num`, `Radon_Nikodym_integrable`,
    `ae_eq_Radon_Nikodym_SigmaFinite`, `Radon_Nikodym_change_of_variables`,
    `Radon_Nikodym_cscale`, `Radon_Nikodym_cadd`, `Radon_Nikodym_chain_rule`
- in `realsum.v`:
  + the following now use `funrpos` and `funrneg`:
    * definition `sum`
    * lemmas `summable_funrpos`, `summable_funrneg`
  + lemma `sum0` (now uses `cst`)

- moved from `realsum` to `numfun.v`:
  + now use `funrpos` and `funrneg`:
    * lemmas `eq_funrpos`, `eq_funrneg`
    * lemma `fpos0` (renamed to `funrpos_cst0`)
    * lemma `fneg0` (renamed to `funrneg_cst0`)
    * lemmas `funrposZ`, `funrnegZ`
    * lemmas `funrpos_natrM`, `funrneg_natrM`
    * lemmas `le_funrpos_norm`

- moved from `numfun.v` to `unstable.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`,
    `decreasing_fun`, `increasing_fun`

- in `esum.v`:
  + definition `esum`
  + lemma `esum_fset`
  + lemma `esum_ge` -> `PosEsum.pos_esum_ge`
  + lemma `le_esum` -> `PosEsum.le_pos_esum`

- moved from `normed_module.v` to `metric_structure.v`
  + lemma `squeeze_cvgr`

- moved from `pseudometric_normed_Zmodule.v` to `metric_structure.v`
  + lemmas `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_le`, `real_cvgr_gt`
  + lemmas `cvgr_lt`, `cvgr_gt`, `cvgr_ge`, `cvgr_le`
- in `normal_distribution.v:
  + `normal_fun_center` -> `normal_fun_center0`

- moved from `measurable_structure.v` to `measure_function.v`:
  + definition `subset_sigma_subadditive`

- moved from `measurable_structure.v` to `unstable.v`:
  + notations `nondecreasing_seq`, `nonincreasing_seq`

- moved from `measurable_structure.v` to `classical_sets.v`:
  + notation `^nat`
  + defintion `sequence`
  + defintion `seqDU`
  + lemmas `seqDU_bigcup_eq`, `trivIset_seqDU`
  + definition `seqD`
  + lemmas `eq_bigcup_seqD`, `trivIset_seqD`, `seqDU_seqD`, `bigcup_bigsetU_bigcup`

- in `functions.v`
  + lemma `fctE` (include `zerofctE` and `onefctE`)

- in `classical_sets.v`
  + lemma `bigcupDr` -> `setD_bigcupr` (deprecating `bigcupDr`)

### Renamed

- in `tvs.v`:
  + definition `tvsType` -> `convexTvsType`
  + class `Tvs` -> `ConvexTvs`
  + mixin `Uniform_isTvs` -> `Uniform_isConvexTvs`
  + factory `PreTopologicalLmod_isTvs` -> `PreTopologicalLmod_isConvexTvs`
  + section `Tvs_numDomain` -> `ConvexTvs_numDomain`
  + section `Tvs_numField` -> `ConvexTvs_numField`
  + section `prod_Tvs` -> `prod_ConvexTvs`

- in `normed_module.v`
  + mixin ` PseudoMetricNormedZmod_Tvs_isNormedModule` ->
    ` PseudoMetricNormedZmod_ConvexTvs_isNormedModule`

- in `measurable_structure.v`:
  + `measurable_prod_measurableType` -> `prod_measurable_rectangle`
  + `sub_sigma_algebra2` -> `sigma_algebra_sub`
- in `measurable_realfun.v`:
  + `measurable_fun_itv_co` -> `measurable_fun_itvbb_itvco`
  + `measurable_fun_itv_oc` -> `measurable_fun_itvbb_itvoc`
  + `emeasurable_fun_itv_cc` -> `emeasurable_fun_itvbb_itvcc`
  + `measurable_fun_itv_cc` -> `measurable_fun_itvbb_itvcc`
  + `measurable_fun_itv_bndo_bndcP` -> `measurable_fun_itvbo_itvbcP`
  + `emeasurable_fun_itv_bndo_bndcP` -> `emeasurable_fun_itvbo_itvbcP`
  + `measurable_fun_itv_obnd_cbndP` -> `measurable_fun_itvob_itvcbP`
  + `emeasurable_fun_itv_obnd_cbndP` -> `emeasurable_fun_itvob_itvcbP`

- in `lebesgue_integral_nonneg.v`:
  + `integral_itv_bndo_bndc` -> `integral_itvbo_itvbc`
  + `integral_itv_obnd_cbnd` -> `integral_itvob_itvcb`
  + `integral_itv_bndoo` -> `integral_itvbb_itvoo`

- in `lebesgue_Rintegral.v`:
  + `Rintegral_itv_bndo_bndc` -> `Rintegral_itvbo_itvbc`
  + `Rintegral_itv_obnd_cbnd` -> `Rintegral_itvob_itvcb`

- in `topology_structure.v`:
  + `cts_fun` -> `continuous_fun`
- in `measure_function.v`:
  + `isFinite` -> `isFinNumFun`
- in `functions_spaces.v`:
  + `weak_sep_cvg` -> `initial_sep_cvg`
  + `weak_sep_nbhsE` -> `initial_sep_nbhsE`
  + `weak_sep_openE` -> `initial_sep_openE`
  + `join_product_weak` -> `join_product_initial`
- in set_interval.v
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

- in `topology_structure.v`:
  + `closure_setC` -> `closureC`
- in `esum.v`:
  + `esum_sum` -> ` exchange_esum_sum`

- in `realsum.v`:
  + `psum` -> `PosSum.psum`

- in `functions.v`
  + lemma `scalrfctE` -> `scalerfctE` (deprecating `scalrfctE`)

### Generalized

- in `measurable_structure.v`:
  + lemma `sigma_algebra_measurable` (not specialized to `setT` anymore)

- in `measurable_function.v`:
  + lemma `preimage_set_system_measurable_fun`

- in `measurable_structure.v`
  + structure `SemiRingOfSets`, mixin `isSigmaRing`, factories `isRingOfSets`,
    `isRingOfSets_setY`, `isAlgebraOfSets`, `isAlgebraOfSets_setD`, `isMeasurable`
    are not required to be pointed anymore
  + lemmas `measurable_g_measurableTypeE`, `g_sigma_algebra_preimageType`,
    `g_sigma_algebra_preimage`, `g_sigma_preimageE`, `g_sigma_preimageE`,
    `g_sigma_algebra_rectangle` are  generalized from `pointedType` to `choiceType`
    (the list might not be exhaustive)

- in `ereal.v`:
  + lemma `funID` generalized from `pointedType` to `Type`

- in `numfun.v`:
  + lemma `indic_restrict` generalized from `pointedType` to `Type`
  + factory `FiniteDecomp` generalized from `pointedType`/`nzRingType` to
    `Type/pzRingType`

- in `simple_functions.v`:
  + lemmas `fctD`, `fctN`, `fctM`, `fctZ`

- in `ereal.v`:
  + lemmas `ge0_mule_fsumr`, `ge0_mule_fsuml`

- in `esum.v`:
  + lemma `esum_set1`

### Deprecated

- file `charge.v` (use `measure.v` and/or `lebesgue_integral.v`)

### Removed

- file `signed.v`

- in `measurable_structure.v`:
  + lemmas `measurable_prod_g_measurableType`, `measurable_prod_g_measurableTypeR`

- file `measurable_structure.v`:
  + notations `preimage_class`, `image_class`, `sigma_algebra_preimage_class`,
    `sigma_algebra_image_class`, `sigma_algebra_preimage_classE` (deprecated since 1.9.0)

- in `ftc.v`:
  + lemma `integrable_locally`

- in `lebesgue_Rintegral.v`:
  + notation `Rintegral_setU_EFin` (deprecated since 1.9.0)

- in `topology_structure.v`:
  + lemma `closureC_deprecated` (deprecated since 1.7.0)

- in `num_normedtype.v`:
  + notation `near_in_itv` (deprecated since 1.7.0)

- in `measurable_fun_approximation.v`:
  + lemma `approximation` (deprecated since 1.8.0)
  + notations `emeasurable_fun_sum`, `emeasurable_fun_fsum`,
    `ge0_emeasurable_fun_sum` (deprecated since 1.8.0)

- in `random_variable.v`:
  + notation `expectationM` (deprecated since 1.8.0)
- in `realsum.v`:
  + definitions `fpos`, `fneg` (use `funrpos`, `funrneg` instead)
  + lemmas `fnegN`, `fposN`
  + lemmas `ge0_pos`, `ge0_neg`
  + lemma `fposBfneg`
  + lemma `funrpos_le`

### Infrastructure

### Misc
