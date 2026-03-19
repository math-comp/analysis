# Changelog (unreleased)

## [Unreleased]

### Added

- in `realfun.v`:
  + lemma `derivable_sqrt`

### Changed

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

### Deprecated

### Removed

### Infrastructure

### Misc
