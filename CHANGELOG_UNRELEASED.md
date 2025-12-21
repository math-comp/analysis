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
  + lemmas `measurable_funN`
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

### Renamed

- in `probability.v`:
  + `derivable_oo_continuous_bnd_onemXnMr` -> `derivable_oo_LRcontinuous_onemXnMr`
- in `measure_negligible.v`:
  + `measure_dominates_ae_eq` -> `null_dominates_ae_eq`

- in `charge.v`:
  + `induced` -> `induced_charge`

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

### Infrastructure

### Misc
