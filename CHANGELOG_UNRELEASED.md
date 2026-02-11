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

### Renamed
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

### Generalized

### Deprecated

### Removed

- in `weak_topology.v`:
  + lemmas `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`,
    `weak_ent_split`, `weak_ent_nbhs`, `weak_pseudo_metric_ball_center`,
    `weak_pseudo_metric_entourageE`
    (now `Let`'s in `initial_topology.v`)

### Infrastructure

### Misc
