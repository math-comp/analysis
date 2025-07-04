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

- in `ftc.v`:
  + lemmas `integration_by_partsy_ge0_ge0`,
           `integration_by_partsy_le0_ge0`,
           `integration_by_partsy_le0_le0`,
           `integration_by_partsy_ge0_le0`

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

- in `unstable.v`:
  + lemma `itv_boundlr_lt`,
  + module `EndlessDense`
    * definitions `is_endless`, `is_dense`
    * lemmas `itv_bound_half_dense`
    * defintions `dual_itv_bound`, `dual_itv`
    * lemmas `dual_itvE`, `dual_itv_sub_memP`, `dual_is_dense`, `dual_is_endless`,
      ` dual_itv_boundK`, `dual_itv_bound_lt`, `dual_itv_bound_le`
    * lemmas `subitvP`, `numDomain_is_endless`, `numField_is_dense`
  + lemma `real_subitvP`

- in `classical_sets.v`:
  + lemma `powerset0`, `powerset1`, `powerset2`, `powersetS`,
    `setorder_itv_setUl_image`, `setorder_itv_setUr_image`,
    `setorder_itv_setDl_image`

- in set_interval.v
  + lemmas `itv_open_endsPn`, `itv_closed_endsPn`, `itv_open_ends_boundlr`

- in topology_structure.v
  + lemmas `closureEbigcap_itvcy`,`interiorEbigcup_itvNyc`,
    `closureEbigcap_itvcc`,`interiorEbigcup_itvcc`

- in num_topology.v
  + module `EndlessDenseTopology` (internal)
  + lemmas `open_itv_open_ends`, `closed_itv_closed_ends`,
    `itv_closureE`, `itv_interiorE`

- in `sequences.v`:
  + lemma `sdrop_shift`
  + lemma `ge_einfs`
  + lemma `einfs_shift`
  + lemma `limn_einf_shift_new`
  + lemma `limn_einf_shiftS`
  + lemma `limn_einf_cst`
- in `uniform_structure.v`:
  + lemma `unif_continuous_continuous`
- in `uniform_structure.v`:
  + lemma `unif_continuous_comp`

- in `initial_topology.v`:
  + lemma `initial_unif_continuous`
  + lemma `initial_unif_continuous_comp`
  + lemma `initial_unif_continuous_comp_fst`
  + lemma `initial_unif_continuous_comp_snd`

- in `product_topology.v`:
  + lemma `entourage_prod_exS`
  + definition `interchange_prod`
  + lemma `entourage_interchange_prod`
  + lemma `pair_unif_continuous`
  + lemma `fst_unif_continuous`
  + lemma `snd_unif_continuous`

- in `metric_space.v`:
  + definition `prod_mdist`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `PseudoMetricNormedZmodule_add_unif_continuous`
  + lemma `PseudoMetricNormedZmodule_opp_unif_continuous`
  + lemma `standard_scale_continuous`
  + notation `topologicalNmodType`

- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

- in `num_normedtype.v`,
  + lemmas `pinftyV`, `ninftyV`, `cvgryV`, `cvgrNyV`, `lt0_cvgMlNy`, 
    `lt0_cvgMrNy`, `lt0_cvgMly`, `lt0_cvgMry`

- in `pseudometric_normed_Zmodule.v`,
  + lemmas `fmap_at_left0P`, `fmap_at_right0E`

- in `unstable.v`:
  + definitions `clamp`, `clamp_gele`
  + lemmas `clamp_gemin`, `clamp_lemax`, `minmax_clamp`,
    `clamp_id`, `clamp_min`, `clamp_max`

- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

- new file `edist.v`

- in `random_variable.v`:
  + lemma `not_range_pmf0`
  + lemma `dRV_esum_pmf_distribution`

- in `measure_theory/measure_function.v`:
  + lemma `semi_cvg_measure_bigcap`
- in `num_normedtype.v`:
  + `continuous_within_itvbbP`,
    `continuous_within_itvocP`, `continuous_within_itvcoP`,
    `continuous_within_itvbyP`, `continuous_within_itvNybP`
- in `num_topology.v`:
  + lemma `not_nearP`
  + lemma `not_nearPball`
- in `pseudometric_structure.v`:
  + lemma `cvg_withinP`

### Changed

- in `esum.v`:
  + level of notation `\esum_ ( i 'in' P ) F`
    from level 41 to 34

- in `lebesgue_integral_definition.v`
  + level of notation `\int[ mu ]_( i 'in' D) F`
    from level 36 to 34 and level of `F` from 36 to 41.
    In particular, this means that `\int[mu]_(x in D) f x * g x`
    now parses as `\int[mu]_(x in D) (f x * g x)`.

- moved from `tvs.v` to `pseudometric_normed_Zmodule.v`:
  + mixin `PreTopologicalNmodule_isTopologicalNmodule`
  + structure `TopologicalNmodule`
  + lemmas `fun_cvgD`, `cvg_sum`, `sum_continuous`
  + mixin `TopologicalNmodule_isTopologicalZmodule`
  + structure `TopologicalZmodule`, type `topologicalZmodType`
  + lemmas `sub_continuous`, `fun_cvgN`
  + factory `PreTopologicalNmodule_isTopologicalZmodule`
  + mixin `PreUniformNmodule_isUniformNmodule`
  + structure `UniformNmodule`
  + mixin `UniformNmodule_isUniformZmodule`
  + structure `UniformZmodule`
  + factory `PreUniformNmodule_isUniformZmodule`
  + lemma `sub_unif_continuous`

- in `tvs.v`:
  + structure `ConvexTvs` now inherits from `UniformZmodule`

- move to `pseudometric_structure.v`:
  + definitions `closed_ball_`, `closed_ball`
  + lemmas `closure_ballE`, `closed_ballxx`, `closed_ball_closed`, `subset_closed_ball`,
    `subset_closure_half`, `le_closed_ball`

- in `topology/topology_structure.v`:
  + lemma `bigcap_open`
- moved to `ereal.v` from `ereal_normedtype.v`:
  + lemma `nbhs_EFin`

- moved to `ereal.v` from `normed_module.v`:
  + lemma `fcvg_is_fine`
  + lemma `fine_fcvg`
  + lemma `cvg_EFin`
  + lemma `fine_cvg`
  + lemma `cvg_is_fine`
  + lemma `fine_cvgP`

- moved to `edist.v` from `urysohn.v`:
  + definitions `edist`, `edist_inf`
  + lemmas `edist_ge0`, `edist_neqNy`, `edist_lt_ball`, `edist_fin`,
    `edist_pinftyP`, `edist_finP`, `edist_fin_open`, `edist_fin_closed`,
    `edist_pinfty_open`, `edist_sym`, `edist_triangle`, `edist_continuous`,
    `edist_closeP`, `edist_refl`, `edist_closel`
  + lemmas `edist_inf_ge0`, `edist_inf_neqNy`, `edist_inf_triangle`,
    `edist_inf_continuous`, `edist_inf0`
- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`

- moved from `tvs.v` to `pseudometric_normed_Zmodule.v`
  and generalized:
  + lemma `nbhsB_subproof`, `nbhsT_subproof`
  + lemma `nbhsB`

- moved from `pseudometric_normed_Zmodule.v` to `num_normedtype.v`:
  + lemmas `continuous_within_itvP`, `continuous_within_itvcyP`, `continuous_within_itvNycP`, `within_continuous_continuous`
- moved from `pseudometric_normed_Zmodule.v` to `num_topology.v`:
  + lemmas `cvg_at_right_filter`,
    `cvg_at_left_filter`, `cvg_at_right_within`, `cvg_at_left_within`

### Renamed

- in `sequences.v`:
  + `limn_einf_shift` -> `limn_einf_addl`
  + `series_le_cvg` -> `series_squeeze_is_cvgn`
- in `pseudometric_normed_Zmodule.v`:
  + `PseudoMetricNormedZmod0` -> `PseudoMetricNormedZmodule`
  + `pseudoMetricNormedZmodType` -> `metricNormedZmodType`
  + `PseudoMetricNormedZmod` -> `MetricNormedZmodule`

- in `normed_module.v`:
  + `PseudoMetricNormedZmod_ConvexTvs_isNormedModule` -> `MetricNormedZmod_ConvexTvs_isNormedModule`
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
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

- in `pseudometric_normed_Zmodule.v`:
  + `continuous_within_itvP` -> `continuous_within_itvccP`

### Generalized

- in `pseudometric_normed_Zmodule.v`:
  + from `pseudoMetricNormedZmodType` to `PseudoMetricNormedZmod0.type`:
    * lemma `le0_ball0`
    * lemma `cvg_bounded`
    * lemma `bounded_cst`
  + from `realFieldType` to `numFieldType`
    * lemma `bounded_funN`
    * lemma `bounded_funD`

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvgD`, `cvg0D`, `cvgD0`, `cvgN`, `cvgNP`, `cvgB`, `cvg0B`, `cvgB0`, `cvgN0`,
    `cvg_sub0`, `cvg0`, `subr_cvg0`
  + lemmas `within_continuousD`, `within_continuousB`, `within_continuousN`
  + lemmas `le_closed_ball`, `closed_ball0`

- in `tvs.v`:
  + lemmas `fun_cvgZ`, `fun_cvgZr`
  + lemmas `nbhsZ`, `nbhs0Z`

- in `esum.v`:
  + lemmas `esum_bigcupT`, `esum_bigcup`

- in `metric_structure.v`:
  + lemmas `metric_sym`, `mdistxx`, `mdist_gt0`
  + lemmas `metric_triangle`, `metric_hausdorff`
- in `measure_theory/measure_function.v`:
  + lemma `cvg_measure_bigcap`

- in `numfun.v`:
  + lemma `itv_partition_nth_ge`
- in `num_normedtype.v`:
    `continuous_within_itvcyP`,
    `continuous_within_itvNycP`, `continuous_within_itvP`,
    `within_continuous_continuous` generalized from `pseudoMetricNormedZmodType` to `pseudoMetricType`
- in `pseudometric_structure.v`:
  + lemma `cvg_nbhsP` generalized from `metricType` to `pseudoMetricType`
- in `realfun.v`:
  + lemmas `cvg_at_rightP`, `cvg_at_leftP`, `cvgr_dnbhsP`, `cvge_at_rightP`, `cvge_at_leftP`, `cvge_dnbhsP` generalized from `realType` to `archiRealFieldType`

### Deprecated

- in `pseudometric_normed_Zmodule.v`:
  + lemma `fun_cvgD` (use `cvgD` instead)
  + lemma `fun_cvgN` (use `cvgN` instead)

### Removed

- in `normed_module.v`,
  + lemmas `cvge_ge` and `cvge_le`, redundant with existing `cvge_to_ge` and `cvge_to_le`
- in `tvs.v`:
  + structure `PreUniformLmodule`
  + mixin `PreUniformLmodule_isUniformLmodule`
  + structure `UniformLmodule`
  + factory `UniformNmodule_isUniformLmodule`
  + lemma `prod_add_continuous` (remains accessible via the generic `add_continuous` of `TopologicalNmodule.type`)

- in `pseudometric_normred_Zmodule.v`:
  + lemma `pseudoMetricNormedZModType_hausdorff` (deprecated since 1.10.0)

### Infrastructure

### Misc
