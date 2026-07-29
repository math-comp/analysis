# Changelog (unreleased)

## [Unreleased]

### Added
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

- in `matrix_normedtype.v`:
  + lemma `within_continuous_coord`


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

- in `normed_module.v`,
  + new lemmas `within_continuousZ`, `within_continuousM`, 
    `within_continuousMl`, and `within_continuousMr`
- in `pseudometric_normed_Zmodule.v`
  + new lemma `within_continuousN`

- in `lebesgue_stieltjes_measure.v`:
  + module `MeasurableRocitv`
  + definition `open_type`
  + notations `.-open`, `.-open.-measurable`
  + module `MeasurableRopen`
    * definition `measurableTypeR`
    + definition `lebesgue_display`
    * definition `measurableR`
    + lemmas `measurable_set1`, `measurable_itv` (also declared as hints)
    + definition `ocitv_measure`, lemma `ocitv_measure_ext`
  + module `MeasurableR`
  + module `RGenOpenSets`
    * lemma `measurableE`

- in `real_interval.v`:
  + lemma `set1_bigcap_oo`

- in `subspace_topology.v`:
  + lemma `cst_within_continuous`

- in `realsum.v`:
  + lemmas `interchange_sup` is no longer
    deprecated and moved to `reals.v`
  + lemma `interchange_psum` is no longer deprecated
- in `distr.v`:
  + lemmas `dlet_dlet`, `dmargin_dlet`, `dlet_dmargin`, `dfst_dswap`,
    `dsnd_dswap`, `dsndE`, `pr_dlet` are no longer deprecated

- in `normed_module.v`:
  + lemmas `cvg1MC`, `cvg1M`, `cvgCM1`, `cvgM1`, `cvg0MC`, `cvg0M`,
    `cvgCM0`, and `cvgM0`
- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvg0D`, `cvg0DC`,
    `cvgD0`, `cvgCD0`, `cvg0B`, `cvg0BC`, `cvgB0`, `cvgCB0`, and `cvgN0`

### Changed

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
