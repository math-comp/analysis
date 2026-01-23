# Changelog (unreleased)

## [Unreleased]

### Added

- in `analysis_stdlib/Rstruct_topology.v`:
  + lemma `RlnE`

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

- in `lebesgue_integrable.v`:
  + lemma `integrable_norm`
- in `order_topology.v`:
  + structures `POrderedNbhs`, `POrderedTopological`, `POrderedUniform`, `POrderedPseudoMetric`,
    `POrderedPointedTopological`
- in `num_topology.v`:
  + lemmas `continuous_rsubmx`, `continuous_lsubmx`

- in `derive.v`:
  + lemmas `differentiable_rsubmx`, `differentiable_lsubmx`
- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

### Changed
- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

### Renamed
- in set_interval.v
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
