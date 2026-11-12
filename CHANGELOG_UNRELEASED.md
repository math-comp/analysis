# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_after`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, `at_right_shift`

- in `realfun.v`:
  + lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`, 
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`,
    `derivable_oo_LRcontinuousS`

- in `metric_structure.v`:
  + lemma `set1_bigcap_ball`

- file `normedtype_measurable.v`
  + definition `borel_type`
  + definition `borel_display`
  + module `MeasurableNormedModuleOpen`
    * lemma `measurable_set1`
    * lemma `measurable_ball_norm`
    * lemma ` measurable_funP1`

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)

- from `lebesgue_stieltjes_measure.v` to (new) `normedtyped_measurable.v`:
  + move definition `open_type`
  + move notations `.-open`, `.-open.-measurable`

- in `lebesgue_stieltjes_measure.v`:
  + sigma-algebra for `\bar R` now uses open sets instead of octiv

### Renamed

- in `lebesgue_stieltjes_measure.v`:
  + `RGenOpens` -> `RGenItvoo`
  + `MeasurableRocitv.measurable_set1` -> `MeasurableRocitv.ocitv_measurable_set1`
  + `MeasurableRocitv.measurable_itv` -> `MeasurableRocitv.ocitv_measurable_itv`

- in `lebesgue_stieltjes_measure.v`:

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

- in `lebesgue_stieltjes_measure.v`:
  + definition `MeasurableRocitv.lebesgue_display`
  + definition `MeasurableRocitv.measurableR`

### Infrastructure

### Misc
