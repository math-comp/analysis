# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_distrl`
  + definition `trivIset`
  + lemmas `trivIset_bigUI`, `trivIset_setI`
- in `ereal.v`:
  + definition `mule` and its notation `*` (scope `ereal_scope`)
  + definition `abse` and its notation `` `| | `` (scope `ereal_scope`)
- in `normedtype.v`:
  + lemmas `closure_sup`, `near_infty_natSinv_lt`, `limit_pointP`
  + lemmas `closure_gt`, `closure_lt`
  + definition `is_interval`, `is_intervalPle`, `interval_is_interval`
  + lemma `connected_intervalP`
  + lemmas `interval_open` and `interval_closed`
  + lemmas `inf_lb_strict`, `sup_ub_strict`, `interval_unbounded_setT`,
    `right_bounded_interior`, `interval_left_unbounded_interior`, `left_bounded_interior`,
    `interval_right_unbounded_interior`, `interval_bounded_interior`
  + definition `Rhull`
  + lemma `sub_Rhull`, `is_intervalP`
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`
  + definitions `isSemiRingOfSets`, `SemiRingOfSets`, notation `semiRingOfSetsType`
  + definitions `RingOfSets_from_semiRingOfSets`, `RingOfSets`, notation `ringOfSetsType`
  + factory: `isRingOfSets`
  + definitions `Measurable_from_ringOfSets`, `Measurable`
  + lemma `semiRingOfSets_measurable{I,D}`
  + definition `diff_fsets`, lemmas `semiRingOfSets_diff_fsetsE`, `semiRingOfSets_diff_fsets_disjoint`
  + definitions `isMeasurable`
  + factory: `isMeasurable`
  + lemma `bigsetU_measurable`, `measurable_bigcap`
  + definitions `semi_additive2`, `semi_additive`, `semi_sigma_additive`
  + lemmas `semi_additive2P`, `semi_additiveE`, `semi_additive2E`,
    `semi_sigma_additive_is_additive`, `semi_sigma_additiveE`
  + `Module AdditiveMeasure`
     * notations `additive_measure`, `{additive_measure set T -> {ereal R}}`
  + lemmas `measure_semi_additive2`, `measure_semi_additive`, `measure_semi_sigma_additive`
  + lemma `semi_sigma_additive_is_additive`, canonical/coercion `measure_additive_measure`
  + lemma `sigma_additive_is_additive`
  + notations `ringOfSetsType`, `outer_measure`
  + definition `negligible` and its notation `.-negligible`
  + lemmas `negligibleP`, `negligible_set0`
  + definition `almost_everywhere` and its notation `{ae mu, P}`
  + lemma `satisfied_almost_everywhere`
  + definition `sigma_subadditive`
  + `Module OuterMeasure`
    * notation `outer_measure`, `{outer_measure set T -> {ereal R}}`
  + lemmas `outer_measure0`, `outer_measure_ge0`, `le_outer_measure`,
    `outer_measure_sigma_subadditive`, `le_outer_measureIC`
- in `boolp.v`:
  + lemmas `and3_asboolP`, `or3_asboolP`, `not_and3P`
- in `classical_sets.v`:
  + lemma `bigcup_sup`
- in `topology.v`:
  + lemmas `closure0`, `separatedC`, `separated_disjoint`, `connectedP`, `connected_subset`,
    `bigcup_connected`
  + definition `connected_component`
  + lemma `component_connected`

### Changed

- in `ereal.v`:
  + notation `x >= y` defined as `y <= x` (only parsing) instead of `gee`
  + notation `x > y` defined as `y < x` (only parsing) instead of `gte`
  + definition `mkset`
  + lemma `eq_set`

### Changed

- in `classical_sets.v`:
  + notation `[set x : T | P]` now use definition `mkset`

### Renamed

- in `classical_sets.v`:
  + `subset_empty` -> `subset_nonempty`
- in `measure.v`:
  + `sigma_additive_implies_additive` -> `sigma_additive_is_additive`
- in `topology.v`:
  + `nbhs_of` -> `locally_of`
- in `topology.v`:
  + `connect0` -> `connected0`

### Removed

### Infrastructure

### Misc
