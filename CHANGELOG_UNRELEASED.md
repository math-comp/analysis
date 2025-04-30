# Changelog (unreleased)

## [Unreleased]

### Added
- in set_interval.v
  + lemmas `setUitv_set2`, `setDitv_set2`, `setDitvoo`, `setDitvoy`, `setDitvNyo`,
    `setDccitv`, `setD_cbnd_bndy`, `setD_bndc_Nybnd`

- in `topology_structure.v`
  + lemma `interiorS`

- in `order_topology.v`
  + lemma `itv_closed_ends_closed`
- in `classical_sets.v`
  + lemma `in_set1_eq`

- in `set_interval.v`
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

- in `Rstruct.v`:
  + lemmas `R0E` and `R1E`
  + multirule `RealsE` to convert from Stdlib reals to Analysis ones

- in `Rstruct_topology.v`:
  + lemma `RlnE`
- in probability.v
  + lemma `pmf_ge0`
  + lemmas `pmf_gt0_countable`, `pmf_measurable`

- in `unstable.v`:
  + lemmas `oppr_itvNy`, `oppr_itvy`
  + lemmas `ltr_norm_bound`, `real_ltr_bound`, `real_ltrNbound`, `ltr_bound`,
    `ltrNbound`

- in `set_interval.v`:
  + lemmas `opp_preimage_itvbndy`, `opp_preimage_itvbndbnd`

- in `lebesgue_measure.v`:
  + lemma `lebesgue_measure_unique`

- in `lebesgue_integral_nonneg.v`:
  + lemmas `lebesgue_measureN`, `ge0_integration_by_substitution0`

- in `measurable_realfun.v`:
  + definition `min_mfun`

- in `random_variable.v`
  + lemmas `lebesgue_integral_pmf`, `cdf_measurable`, `ccdf_measurable`,
    `le0_expectation_cdf`

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_setU`

- in `measurable_realfun.v`:
  + lemmas `emeasurable_fun_itv_obnd_cbndP`, `emeasurable_fun_itv_bndo_bndcP`,
    `emeasurable_fun_itv_cc`
- in `normed_module.v`:
  + lemma `open_subball_rat`
  + fact `isolated_rat_ball`
  + lemma `countable_isolated`
- in `normed_module.v`:
  + lemma `limit_point_setD`

- in `reals.v`:
  + lemma `nat_has_minimum`

- in `sequences.v`:
  + lemma `cluster_eventuallyP`
  + lemmas `cluster_eventually_cvg`, `limit_point_cluster_eventually`

- in `lebesgue_integrable.v`:
  + lemma `integrable_set0`
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

- in `measurable_function.v`:
  + lemma `preimage_set_system_compS`

- in `numfun.v`:
  + defintions `funrpos`, `funrneg` with notations `^\+` and `^\-`
  + lemmas `funrpos_ge0`, `funrneg_ge0`, `funrposN`, `funrnegN`, `ge0_funrposE`,
    `ge0_funrnegE`, `le0_funrposE`, `le0_funrnegE`, `ge0_funrposM`, `ge0_funrnegM`,
    `le0_funrposM`, `le0_funrnegM`, `funr_normr`, `funrposneg`, `funrD_Dpos`,
    `funrD_posD`, `funrpos_le`, `funrneg_le`
  + lemmas `funerpos`, `funerneg`

- in `measurable_structure.v`:
  + definitions `preimage_display`, `g_sigma_algebra_preimageType`, `g_sigma_algebra_preimage`,
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
  + lemmas `independent_RVs2_comp`, `independent_RVs2_funrposneg`,
    `independent_RVs2_funrnegpos`, `independent_RVs2_funrnegneg`,
    `independent_RVs2_funrpospos`
  + lemma `expectationM_ge0`, `integrable_expectationM`, `independent_integrableM`,
    ` expectation_prod`

- in `numfun.v`
  + lemmas `funeposE`, `funenegE`, `funepos_comp`, `funeneg_comp`

- in `classical_sets.v`:
  + lemmas `xsectionE`, `ysectionE`

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

- in `lebesgue_integrable.v`:
  + lemma `integrable_norm`
- in `order_topology.v`:
  + structures `POrderedNbhs`, `POrderedTopological`, `POrderedUniform`, `POrderedPseudoMetric`,
    `POrderedPointedTopological`

- in `subtype_topology.v`:
  + lemma `within_continuous_comp`

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `within_continuousB`, `within_continuousD`

- in `normed_module.v`:
  + lemma `within_continuous_compN`
- in `normed_module.v`:
  + lemma `compact_has_sup`

- in `derive.v`:
  + lemmas `compact_EVT_max`, `compact_EVT_min`, `EVT_max_rV`, `EVT_min_rV`

### Changed
- in set_interval.v
  + `setUitv1`, `setU1itv`, `setDitv1l`, `setDitv1r` (generalized)

- in `set_interval.v`
  + `itv_is_closed_unbounded` (fix the definition)

- in `set_interval.v`
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

- moved from `convex.v` to `realfun.v`
  + lemma `second_derivative_convex`

- in classical_sets.v
  + lemma `in_set1` (statement changed)

- in `subspace_topology.v`:
  + lemmas `open_subspaceP` and `closed_subspaceP` (use `exists2` instead of `exists`)

### Renamed

- in `topology_structure.v`
  + `closure_subset` -> `closureS`

- in `set_interval.v`:
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

- `weak_topology.v` -> `initial_topology.v`
  + `weak_topology` -> `initial_topology`
  + `weak_continuous` -> `initial_continuous`
  + `weak_ent` -> `initial_ent`
  + `weak_ball` -> `initial_ball`
  + `weak_ballE` -> `initial_ballE`
  + `open_order_weak` -> `open_order_initial`
  + `continuous_comp_weak` -> `continuous_comp_initial`

- in `one_point_compactification.v`:
  + `one_point_compactification_weak_topology` ->
    `one_point_compactification_initial_topology`

- in `subspace_topology.v`:
  + `weak_subspace_open` -> `initial_subspace_open`

- in `functions_spaces.v`:
  + `weak_sep_cvg` -> `initial_sep_cvg`
  + `weak_sep_nbhsE` -> `initial_sep_nbhsE`
  + `weak_sep_openE` -> `initial_sep_openE`
  + `join_product_weak` -> `join_product_initial`

- in `lebesgue_integral_nonneg.v`:
  + `integral_setD1_EFin` -> `integral_setD1`
- in `charge.v`:
  + `induced` -> `induced_charge`
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

- in `topology_structure.v`:
  + `closed_comp` -> `preimage_closed`
  + `clopen_comp` -> `preimage_clopen`

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`,
    `integral_itv_bndoo`

### Deprecated

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_setU_EFin`

### Removed

- in `weak_topology.v`:
  + lemmas `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`,
    `weak_ent_split`, `weak_ent_nbhs`, `weak_pseudo_metric_ball_center`,
    `weak_pseudo_metric_entourageE`
    (now `Let`'s in `initial_topology.v`)

- in `measurable_realfun.v`:
  + lemma `max_mfun_subproof` (has become a `Let`)

- in `simple_functions.v`:
  + definition `max_sfun`

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_setU` (was deprecated since version 1.0.1)
- in `measure_function.v`:
  + notations `g_salgebra_measure_unique_trace`,
    `g_salgebra_measure_unique_cover`, `g_salgebra_measure_unique`
    (deprecated since 1.2.0)

- in `measurable_structure.v`:
  + notations `monotone_class`, `monotone_class_g_salgebra`,
    `smallest_monotone_classE`, `monotone_class_subset`,
    `setI_closed_gdynkin_salgebra`, `dynkin_g_dynkin`, `dynkin_monotone`,
    `salgebraType`
    (deprecated since 1.2.0)

- in `sequences.v`:
  + notation `eq_bigsetU_seqD`
    (deprecated since 1.2.0)
- in `measurable_structure.v`:
  + definition `measure_dominates` (use `null_set_dominates` instead)
  + lemma `measure_dominates_trans`

- in `charge.v`:
  + lemma `dominates_charge_variation` (use `charge_null_dominatesP` instead)

- in `set_interval.v`:
  + lemma `interval_set1` (use `set_itv1` instead)
- in `ereal.v`:
  + notation `ereal_sup_le` (was deprecated since 1.11.0)

- in `boolp.v`:
  + notation `eq_exists2` (was deprecated since version 1.10.0)

### Infrastructure

### Misc
