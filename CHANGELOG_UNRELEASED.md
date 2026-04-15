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

- in `measurable_structure.v`:
  + lemmas `g_sigma_algebra_cross`, `g_sigma_algebra_rectangle`

- in `measurable_function.v`:
  + lemma `preimage_measurability`

### Changed

- moved from `measurable_structure.v` to `classical_sets.v`:
  + definition `preimage_set_system`
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
    `preimage_set_system_id`
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
  + definitions `lcfun`, `lcfun_key, `lcfunP`
  + lemmas `lcfun_eqP`, `null_fun_continuous`, `fun_cvgD`,
   `fun_cvgN`, `fun_cvgZ`, `fun_cvgZr`
  + lemmas `lcfun_continuous` and `lcfun_linear`
  
### Changed

- moved from `topology_structure.v` to `filter.v`:
  + lemma `continuous_comp` (and generalized)

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

### Generalized

- in `measurable_structure.v`:
  + lemma `sigma_algebra_measurable` (not specialized to `setT` anymore)

### Deprecated

### Removed

- in `measurable_structure.v`:
  + lemmas `measurable_prod_g_measurableType`, `measurable_prod_g_measurableTypeR`

### Infrastructure

### Misc
