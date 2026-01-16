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

- in `measurable_structure.v`:
  + lemmas `g_sigma_algebra_cross`, `g_sigma_algebra_rectangle`

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

### Changed

- moved from `measurable_structure.v` to `classical_sets.v`:
  + definition `preimage_set_system`
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
    `preimage_set_system_id`
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
  
### Changed

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
  + `itv_is_ray` -> `itv_is_open_unbounded`,
  + `itv_is_bd_open` -> `itv_is_oo`,

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

### Deprecated

- file `charge.v` (use `measure.v` and/or `lebesgue_integral.v`)

### Removed

- file `signed.v`

- in `measurable_structure.v`:
  + lemmas `measurable_prod_g_measurableType`, `measurable_prod_g_measurableTypeR`

### Infrastructure

### Misc
