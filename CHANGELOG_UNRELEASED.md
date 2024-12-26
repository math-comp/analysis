# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `nonemptyPn`

- in `cardinality.v`:
  + lemma `infinite_setD`

- in `convex.v`:
  + lemmas `convN`, `conv_le`

- in `normed_module.v`:
  + lemma `limit_point_infinite_setP`
- in `measure_negligible.v`:
  + definition `null_set` with notation `_.-null_set`
  + lemma `subset_null_set`
  + lemma `negligible_null_set`
  + lemma `measure0_null_setP`
  + lemma `null_setU`
  + definition `null_dominates`
  + lemma `null_dominates_trans`
  + lemma `null_content_dominatesP`

- in `charge.v`:
  + definition `charge_dominates`
  + lemma `charge_null_dominatesP`
  + lemma `content_charge_dominatesP`

- in `sequences.v`:
  + lemma `increasing_seq_injective`
  + definition `adjacent_set`
  + lemmas `adjacent_sup_inf`, `adjacent_sup_inf_unique`
  + definition `cut`
  + lemmas `cut_adjacent`, `infinite_bounded_limit_point_nonempty`

- in `measurable_structure.v`:
  + lemma `dynkin_induction``

- in `lebesgue_integral_fubini.v`:
  + definition `product_subprobability`
  + lemma `product_subprobability_setC`

- in `lebesgue_integral_theory/lebesgue_integrable.v`
  + lemma `null_set_integrable`

- new file `lebesgue_integral_theory/giry.v`
  + definition `measure_eq`
  + definition `giry`
  + definition `giry_ev`
  + definition `giry_measurable`
  + definition `preimg_giry_ev`
  + definition `giry_display`
  + lemma `measurable_giry_ev`
  + definition `giry_int`
  + lemmas `measurable_giry_int`, `measurable_giry_codensity`
  + definition `giry_map`
  + lemmas `measurable_giry_map`, `giry_int_map`, `giry_map_dirac`
  + definition `giry_ret`
  + lemmas `measurable_giry_ret`, `giry_int_ret`
  + definition `giry_join`
  + lemmas `measurable_giry_join`, `sintegral_giry_join`, `giry_int_join`
  + definition `giry_bind`
  + lemmas `measurable_giry_bind`, `giry_int_bind`
  + lemmas `giry_joinA`, `giry_join_id1`, `giry_join_id2`, `giry_map_zero`
  + definition `giry_prod`
  + lemmas `measurable_giry_prod`, `giry_int_prod1`, `giry_int_prod2`

- in `measurable_realfun.v`:
  + lemma `measurable_funN`
  + lemmas `nondecreasing_measurable`, `nonincreasing_measurable`
- in `subspace_topology.v`:
  + definition `from_subspace`
- in `topology_structure.v`:
  + definition `isolated`
  + lemma `isolatedS`
  + lemma `disjoint_isolated_limit_point`
  + lemma `closure_isolated_limit_point`

- in `separation_axioms.v`:
  + lemma `perfectP`

- in `cardinality.v`:
  + lemmas `finite_setX_or`, `infinite_setX`
  + lemmas `infinite_prod_rat`, ``card_rat2`

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
- in `probability.v`:
  + lemmas `eq_bernoulli`, `eq_bernoulliV2`
- file `mathcomp_extra.v`
  + lemmas `ge_trunc`, `lt_succ_trunc`, `trunc_ge_nat`, `trunc_lt_nat`

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)
  + lemmas `RabsE`, `RdistE`, `sum_f_R0E`, `factE`

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- in `numfun.v`:
  + defintions `funrpos`, `funrneg` with notations `^\+` and `^\-`
  + lemmas `funrpos_ge0`, `funrneg_ge0`, `funrposN`, `funrnegN`, `ge0_funrposE`,
    `ge0_funrnegE`, `le0_funrposE`, `le0_funrnegE`, `ge0_funrposM`, `ge0_funrnegM`,
    `le0_funrposM`, `le0_funrnegM`, `funr_normr`, `funrposneg`, `funrD_Dpos`,
    `funrD_posD`, `funrpos_le`, `funrneg_le`
  + lemmas `funerpos`, `funerneg`

- in `measure.v`:
  + lemma `preimage_class_comp`
  + defintions `preimage_display`, `g_sigma_algebra_preimageType`, `g_sigma_algebra_preimage`,
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

### Changed

- in `charge.v`:
  + `dominates_cscalel` specialized from
    `set _ -> \bar _` to `{measure set _ -> \bar _}`

- in `measurable_structure.v`:
  + the notation ``` `<< ``` is now for `null_set_dominates`,
    the previous definition can be recovered with the lemma
    `null_dominatesP`

- in `lebesgue_integral_monotone_convergence.v`:
  + lemma `ge0_le_integral` (remove superfluous hypothesis)
- in `subspace_topology.v`:
  + notation `{within _, continuous _}` (now uses `from_subspace`)

- moved from `realfun.v` to `numfun.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`, `increasing_fun`,
    `decreasing_fun`
  + generalized from `realType` to `numDomainType`:
    * lemmas `nondecreasing_funN`, `nonincreasing_funN`
  + generalized from `realType` to `porderType`
    * definitions `itv_partition`, `itv_partitionL`, `itv_partitionR`
    * lemmas `itv_partition_nil`, `itv_partition_cons`, `itv_partition1`,
      `itv_partition_size_neq0`, `itv_partitionxx`, `itv_partition_le`,
      `itv_partition_cat`, `itv_partition_nth_size`, `itv_partition_nth_ge`,
      `itv_partition_nth_le`, `nondecreasing_fun_itv_partition`
  + generalized from `realType` to `orderType`
    * lemmas `itv_partitionLP`, `itv_partitionRP`, `in_itv_partition`,
      `notin_itv_partition`
  + generalize from `realType` to `numDomainType`:
    * lemmas `nonincreasing_fun_itv_partition`, `itv_partition_rev`

- moved from `realfun.v` to `numfun.v`:
  + generalize from `realType` to `numDomainType`
    * definition `variation`
    * lemmas `variation_zip`, `variation_prev`, `variation_next`,
      `variation_nil`, `variation_ge0`, `variationN`, `variation_le`,
      `nondecreasing_variation`, `nonincreasing_variation`,
      `variation_cat` (order of parameters also changed), `le_variation`,
      `variation_opp_rev`, `variation_rev_opp`
  + generalize from `realType` to `realDomainType`
    * lemmas `variation_itv_partitionLR`, `variation_subseq`

- moved from `realfun.v` to `numfun.v`:
  + generalize from `realType` to `numDomainType`
    * definition `variations`, `bounded_variation`
    * lemmas `variations_variation`, `variations_neq0`, `variationsN`,
      `variationsxx`
    * lemmas `bounded_variationxx`, `bounded_variationD`,
      `bounded_variationN`, `bounded_variationl`, `bounded_variationr`,
      `variations_opp`, `nondecreasing_bounded_variation`

### Renamed

- in `probability.v`:
  + `derivable_oo_continuous_bnd_onemXnMr` -> `derivable_oo_LRcontinuous_onemXnMr`
- in `measure_negligible.v`:
  + `measure_dominates_ae_eq` -> `null_dominates_ae_eq`

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
- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`
- in `lebesgue_integral.v`:
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`
  + `measurable_funP` -> `measurable_funPT` (field of `isMeasurableFun` mixin)

- in `mathcomp_extra.v`
  + `comparable_min_le_min` -> `comparable_le_min2`
  + `comparable_max_le_max` -> `comparable_le_max2`
  + `min_le_min` -> `le_min2`
  + `max_le_max` -> `le_max2`
  + `real_sqrtC` -> `sqrtC_real`
- in `measure.v`
  + `preimage_class` -> `preimage_set_system`
  + `image_class` -> `image_set_system`
  + `preimage_classes` -> `g_sigma_preimageU`
  + `preimage_class_measurable_fun` -> `preimage_set_system_measurable_fun`
  + `sigma_algebra_preimage_class` -> `sigma_algebra_preimage`
  + `sigma_algebra_image_class` -> `sigma_algebra_image`
  + `sigma_algebra_preimage_classE` -> `g_sigma_preimageE`
  + `preimage_classes_comp` -> `g_sigma_preimageU_comp`
  
### Renamed

- in `lebesgue_measure.v`:
  + `measurable_fun_indic` -> `measurable_indic`
  + `emeasurable_fun_sum` -> `emeasurable_sum`
  + `emeasurable_fun_fsum` -> `emeasurable_fsum`
  + `ge0_emeasurable_fun_sum` -> `ge0_emeasurable_sum`
- in `probability.v`:
  + `expectationM` -> `expectationZl`

- in `classical_sets.v`:
  + `preimage_itv_o_infty` -> `preimage_itvoy`
  + `preimage_itv_c_infty` -> `preimage_itvcy`
  + `preimage_itv_infty_o` -> `preimage_itvNyo`
  + `preimage_itv_infty_c` -> `preimage_itvNyc`

- in `constructive_ereal.v`:
  + `maxeMr` -> `maxe_pMr`
  + `maxeMl` -> `maxe_pMl`
  + `mineMr` -> `mine_pMr`
  + `mineMl` -> `mine_pMl`

- in `probability.v`:
  + `integral_distribution` -> `ge0_integral_distribution`

- file `homotopy_theory/path.v` -> `homotopy_theory/continuous_path.v`

### Generalized

- in `lebesgue_integral_under.v`:
  + weaken an hypothesis of lemma `continuity_under_integral`

- in `lebesgue_integrable.v`:
  + weaken an hypothesis of lemma `finite_measure_integrable_cst`

- in `derive.v`:
  + definition `jacobian`
  + lemmas `deriveEjacobian`, `differentiable_coord`

- in `ftc.v`:
  + lemmas `parameterized_integral_continuous`,
    `integration_by_substitution_decreasing`,
    `integration_by_substitution_oppr`,
    `integration_by_substitution_increasing`,
    `integration_by_substitution_onem`,
    `Rintegration_by_substitution_onem`

- in `lebesgue_integral_theory/lebesgue_integrable.v`
  + lemma `null_set_integral`

- in `realfun.v`:
  + generalized from `realType` to `realFieldType`:
    * definition `total_variation`
    * lemmas `total_variationxx`, `nondecreasing_total_variation`,
      `total_variationN`

- in `num_topology.v`:
  + lemma `in_continuous_mksetP`

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `continuous_within_itvP`, `continuous_within_itvcyP`,
    `continuous_within_itvNycP`
  + lemma `within_continuous_continuous`
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`, `realFieldType`

### Deprecated

- in `topology_structure.v`:
  + lemma `closure_limit_point` (use `closure_limit_point_isolated` instead)

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
- in `measurable_structure.v`:
  + definition `measure_dominates` (use `null_set_dominates` instead)
  + lemma `measure_dominates_trans`

- in `charge.v`:
  + lemma `dominates_charge_variation` (use `charge_null_dominatesP` instead)

- in `set_interval.v`:
  + lemma `interval_set1` (use `set_itv1` instead)
- in `ereal.v`:
  + notation `ereal_sup_le` (was deprecated since 1.11.0)
- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)
  + lemma `deg_le2_ge0` (available as `deg_le2_poly_ge0` in `ssrnum.v`
    since MathComp 2.1.0)
- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)
- in `topology_structure.v`:
  + lemma `closureC`

- in file `lebesgue_integral.v`:
  + lemma `approximation`

### Removed

- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`

- in `cardinality.v`:
  + lemma `cst_fimfun_subproof`

- in `lebesgue_integral.v`:
  + lemma `cst_mfun_subproof` (use lemma `measurable_cst` instead)
  + lemma `cst_nnfun_subproof` (turned into a `Let`)
  + lemma `indic_mfun_subproof` (use lemma `measurable_fun_indic` instead)

- in `lebesgue_integral.v`:
  + lemma `measurable_indic` (was uselessly specializing `measurable_fun_indic` (now `measurable_indic`) from `lebesgue_measure.v`)
  + notation `measurable_fun_indic` (deprecation since 0.6.3)
- in `constructive_ereal.v`
  + notation `lee_opp` (deprecated since 0.6.5)
  + notation `lte_opp` (deprecated since 0.6.5)
- in `measure.v`:
  + `dynkin_setI_bigsetI` (use `big_ind` instead)

- in `lebesgue_measurable.v`:
  + notation `measurable_fun_power_pos` (deprecated since 0.6.3)
  + notation `measurable_power_pos` (deprecated since 0.6.4)

### Infrastructure

### Misc
