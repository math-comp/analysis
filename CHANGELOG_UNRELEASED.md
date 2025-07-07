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

- in `classical_sets.v`:
  + lemmas `setUDl`, `setUDr`

- in `cardinality.v`:
  + notation `cofinite_set`
  + lemmas `cofinite_setT`, `infinite_setN0`, `sub_cofinite_set`,
    `sub_infinite_set`, `cofinite_setUl`, `cofinite_setUr`, `cofinite_setU`,
    `cofinite_setI`, `cofinite_set_infinite`, `infinite_setIl`,
    `infinite_setIr`
  + lemma `injective_gtn`

- in `sequences.v`:
  + lemma `finite_range_cst_subsequence`
  + lemmas `infinite_increasing_seq`, `infinite_increasing_seq_wf`
  + lemma `finite_range_cvg_subsequence`
  + theorem `bolzano_weierstrass`

- in `lebesgue_integrable.v`:
  + lemma `integrable_norm`
- in `order_topology.v`:
  + structures `POrderedNbhs`, `POrderedTopological`, `POrderedUniform`, `POrderedPseudoMetric`,
    `POrderedPointedTopological`
- in `num_topology.v`:
  + lemmas `continuous_rsubmx`, `continuous_lsubmx`

- in `derive.v`:
  + lemmas `differentiable_rsubmx`, `differentiable_lsubmx`

- in `unstable.v`:
  + definitions `monotonic`, `strict_monotonic`
  + lemma `strict_monotonicW`

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
- in `Rstruct.v`:
  + lemmas `RleP`, `RltP` (change implicits)
- new file `metric_structure.v`:
  + mixin `isMetric`, structure `Metric`, type `metricType`
    * with fields `mdist`, `mdist_ge0`, `mdist_positivity`, `ballEmdist`
  + lemmas `metric_sym`, `mdistxx`, `mdist_gt0`, `metric_triangle`,
    `metric_hausdorff`
  + `R^o` declared to be an instance of `metricType`
  + module `metricType_numDomainType`
    * lemmas `ball_mdistE`, `nbhs_nbhs_mdist`, `nbhs_mdistP`,
      `filter_from_mdist_nbhs`, `fcvgrPdist_lt`, `cvgrPdist_lt`,
      `cvgr_dist_lt`, `cvgr_dist_le`, `nbhsr0P`, `cvgrPdist_le`

- in `pseudometric_normed_Zmodule.v`:
  + factory `NormedZmoduleMetric` with field `mdist_norm`

### Changed

- moved from `pseudometric_normed_Zmodule.v` to `num_topology.v`:
  + notations `^'+`, `^'-`
  + definitions `at_left`, `at_right`
  + instances `at_right_proper_filter`, `at_left_proper_filter`
  + lemmas `nbhs_right_gt`, `nbhs_left_lt`, `nbhs_right_neq`, `nbhs_left_neq`,
    `nbhs_left_neq`, `nbhs_left_le`, `nbhs_right_lt`, `nbhs_right_ltW`,
    `nbhs_right_ltDr`, `nbhs_right_le`, `not_near_at_rightP`

- moved from `realfun.v` to `metric_structure.v` and generalized:
  + lemma `cvg_nbhsP`

### Renamed

- in `probability.v`:
  + `derivable_oo_continuous_bnd_onemXnMr` -> `derivable_oo_LRcontinuous_onemXnMr`
- in `measure_negligible.v`:
  + `measure_dominates_ae_eq` -> `null_dominates_ae_eq`

- in `charge.v`:
  + `induced` -> `induced_charge`

- in `boolp.v`:
  + `notP` -> `not_notP`
  + `notE` -> `not_notE`

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
- in `num_normedtype.v`:
  + weaken hypothesis in lemmas `mono_mem_image_segment`, `mono_surj_image_segment`,
    `inc_surj_image_segment`, `dec_surj_image_segment`, `inc_surj_image_segmentP`,
    `dec_surj_image_segmentP`, `mono_surj_image_segmentP`

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

- in `unstable.v`:
  + definition `monotonous` (use `strict_monotonic` instead)

### Infrastructure

### Misc
