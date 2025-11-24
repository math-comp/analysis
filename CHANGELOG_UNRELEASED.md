# Changelog (unreleased)

## [Unreleased]

### Added

- in `cardinality.v`:
  + lemma `infinite_setD`

- in `convex.v`:
  + lemmas `convN`, `conv_le`

- in `normed_module.v`:
  + lemma `limit_point_infinite_setP`

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

### Infrastructure

### Misc
