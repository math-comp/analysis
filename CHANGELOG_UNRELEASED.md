# Changelog (unreleased)

## [Unreleased]

### Added

- in `cardinality.v`:
  + lemma `infinite_setD`

- in `convex.v`:
  + lemmas `convN`, `conv_le`

- in `normed_module.v`:
  + lemma `limit_point_infinite_setP`
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

### Changed

### Renamed

- in `probability.v`:
  + `derivable_oo_continuous_bnd_onemXnMr` -> `derivable_oo_LRcontinuous_onemXnMr`
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

### Generalized

- in `lebesgue_integral_under.v`:
  + weaken an hypothesis of lemma `continuity_under_integral`

- in `lebesgue_integrable.v`:
  + weaken an hypothesis of lemma `finite_measure_integrable_cst`

### Deprecated

### Removed

- in `lebesgue_stieltjes_measure.v`:
  + notation `wlength_sigma_sub_additive` (deprecated since 1.1.0)

- in `constructive_ereal.v`:
  + notations `gee_pmull`, `gee_addl`, `gee_addr`, `gte_addr`, `gte_addl`,
    `lte_subl_addr`, `lte_subl_addl`, `lte_subr_addr`, `lte_subr_addl`,
    `lee_subl_addr`, `lee_subl_addl`, `lee_subr_addr`, `lee_subr_addl`
    (deprecated since 1.2.0)

- in `signed.v`:
  + notations `num_le_maxr`, `num_le_maxl`, `num_le_minr`, `num_le_minl`,
    `num_lt_maxr`, `num_lt_maxl`, `num_lt_minr`, `num_lt_minl`
    (deprecated since 1.2.0)

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
- in `ereal.v`:
  + notation `ereal_sup_le` (was deprecated since 1.11.0)

### Infrastructure

### Misc
