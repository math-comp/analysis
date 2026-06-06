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
- in `borel_hierarchy.v`:
  + definition `borel_type`
  + lemmas `singleton_bigcap`, `measurable1`

- in `simple_functions.v`:
  + lemmas `sfun_op`, `sfun_submod_closed`
  + `{sfun aT >-> borel_type V}` is an `lmodType` when `V` is a `normedModType`

- in `set_interval.v`:
  + lemmas `setU_itvob1`, `setU_1itvob`

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
  + structure `SimpleFun` (and notation `{sfun aT >-> _}`): codomain
    generalized from `realType` to `sigmaRingType d'`, adding a display parameter `d'`;

- in `ereal.v`:
  + lemmas `ge0_mule_fsumr`, `ge0_mule_fsuml`

- in `esum.v`:
  + lemma `esum_set1`

### Deprecated

### Removed

- in `lebesgue_stieltjes_measure.v`:
  + definition `MeasurableRocitv.lebesgue_display`
  + definition `MeasurableRocitv.measurableR`

### Infrastructure

### Misc
