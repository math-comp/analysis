# Changelog (unreleased)

## [Unreleased]

### Added

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

### Renamed

- in `tvs.v`:
  + definition `tvsType` -> `convexTvsType`
  + HB class `Tvs` -> `ConvexTvs`
  + HB mixin `Uniform_isTvs` -> `Uniform_isConvexTvs`
  + HB factory `PreTopologicalLmod_isTvs` -> `PreTopologicalLmod_isConvexTvs`
  + Section `Tvs_numDomain` -> `ConvexTvs_numDomain`
  + Section `Tvs_numField` -> `ConvexTvs_numField`
  + Section `prod_Tvs` -> `prod_ConvexTvs`

- in `normed_module.v`
  + HB mixin ` PseudoMetricNormedZmod_Tvs_isNormedModule` ->
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
