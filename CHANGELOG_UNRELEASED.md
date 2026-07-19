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
- in `normed_module.v`,
  + new lemmas `within_continuousZ`, `within_continuousM`, 
    `within_continuousMl`, and `within_continuousMr`
- in `pseudometric_normed_Zmodule.v`
  + new lemma `within_continuousN`

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

- moved from `realfun.v` to `derive.v` and generalized:
  + lemmas `is_deriveV`, `is_derive1_comp`
- moved from `measurable_realfun.v` to `lebesgue_stieltjes_measure.v`
  + module `RGenOInfty`
  + module `RGenInftyO`
  + module `RGenCInfty`
  + module `RGenOpens`

- moved inside module `MeasurableRocitv` (`lebesgue_stieltjes_measure.v`):
  + lemmas `measurable_set1`, `measurable_itv`

- in `lebesgue_stieltjes_measure.v`:
  + lemma `lebesgue_stieltjes_measure_unique` is now about the sigma-algebra generated by open sets
- moved from `realfun.v` to `derive.v` and generalized:
  + lemmas `is_deriveV`, `is_derive1_comp`

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
