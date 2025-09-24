# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemma `ltgte_fin_num`

- in `probability.v`:
  + lemmas `cdf_fin_num`, `lebesgue_stieltjes_cdf_id`

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


- file `mathcomp_extra.v`
  + lemmas `ge_trunc`, `lt_succ_trunc`, `trunc_ge_nat`, `trunc_lt_nat`

- in `measure.v`:
  + lemma `preimage_set_system_compS`

- in `numfun.v`:
  + defintions `funrpos`, `funrneg` with notations `^\+` and `^\-`
  + lemmas `funrpos_ge0`, `funrneg_ge0`, `funrposN`, `funrnegN`, `ge0_funrposE`,
    `ge0_funrnegE`, `le0_funrposE`, `le0_funrnegE`, `ge0_funrposM`, `ge0_funrnegM`,
    `le0_funrposM`, `le0_funrnegM`, `funr_normr`, `funrposneg`, `funrD_Dpos`,
    `funrD_posD`, `funrpos_le`, `funrneg_le`
  + lemmas `funerpos`, `funerneg`

- in `measure.v`:
  + lemma `preimage_class_comp`
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

- in `lebesgue_stieltjes_measure.v` specialized from `numFieldType` to `realFieldType`:
  + lemma `nondecreasing_right_continuousP` 
  + definition `CumulativeBounded`

- in `lebesgue_stieltjes_measure.v`, according to generalization of `Cumulative`, modified:
  + lemmas `wlength_ge0`, `cumulative_content_sub_fsum`, `wlength_sigma_subadditive`, `lebesgue_stieltjes_measure_unique`
  + definitions `lebesgue_stieltjes_measure`, `completed_lebesgue_stieltjes_measure`

- moved from `vitali_lemma.v` to `pseudometric_normed_Zmodule.v` and renamed:
  + `closure_ball` -> `closure_ballE`

### Renamed

### Generalized

- in `pseudometric_normed_Zmodule.v`:
  + lemma `closed_ball0` (`realFieldType` -> `pseudoMetricNormedZmodType`)
  + lemmas `closed_ball_closed`, `subset_closed_ball` (`realFieldType` -> `numDomainType`)
  + lemma `subset_closure_half` (`realFieldType` -> `numFieldType`)
  + lemma `le_closed_ball` (`pseudoMetricNormedZmodType` -> `pseudoMetricType`)

- in `lebesgue_stieltjes_measure.v` generalized (codomain is now an `orderNbhsType`):
  + lemma `right_continuousW`
  + record `isCumulative`
  + definition `Cumulative`

### Deprecated

### Removed

- file `interval_inference.v` (now in MathComp)

- in file `all_reals.v`
  + export of `interval_inference` (now in mathcomp-algebra, but not automatically exported)

### Infrastructure

### Misc
