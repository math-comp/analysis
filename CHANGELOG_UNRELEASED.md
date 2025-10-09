# Changelog (unreleased)

## [Unreleased]

### Added

- in `set_interval.v`:
  + lemmas `itv_setU_setT`, `disjoint_rays`

- in `constructive_ereal.v`:
  + lemma `ltgte_fin_num`

- in `probability.v`:
  + definition `ccdf`
  + lemmas `cdf_fin_num`, `lebesgue_stieltjes_cdf_id`, `cdf_ccdf_1`, `ccdf_fin_num`, `ccdf_nonincreasing`, `cvg_ccdfy0`, `cvg_ccdfNy1`, `ccdf_right_continuous`
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

### Changed

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

- in `set_interval.v`:
  + lemma `set_itv_splitI` (generalized from `orderType` to `porderType`)
  + lemma `disjoint_itvxx` (generalized from `numDomainType` to `porderType`)
  + lemma `disjoint_neitv` (generalized from `realFieldType` to `orderType`)

- in `probabilitity.v`:
  + lemma `exponential_pdf_ge0` (hypothesis generalized)

### Deprecated

### Removed

- file `interval_inference.v` (now in MathComp)

- in file `all_reals.v`
  + export of `interval_inference` (now in mathcomp-algebra, but not automatically exported)
- file `theories/measure.v`
- notations `[measure of _]`, `[measure of _]`
- notations `[content of _]`, `[content of _]`
- notations `[outer_measure of _]`, `[outer_measure of _]`

### Infrastructure

### Misc
