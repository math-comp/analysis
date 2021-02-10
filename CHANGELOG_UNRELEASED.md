# Changelog (unreleased)

## [Unreleased]

### Added
  
- in `topology.v`:
  + global instance `ball_filter`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pointedType`, `filteredType`, `topologicalType`,
      `uniformType`, `pseudoMetricType`
  + module `numFieldTopology` with an `Exports` submodule
    * many canonicals and coercions
  + global instance `Proper_nbhs'_regular_numFieldType`
- in `normedtype.v`:
  + definitions `ball_`, `pointed_of_zmodule`, `filtered_of_normedZmod`
  + lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`
  + definition `pseudoMetric_of_normedDomain`
  + lemma `nbhs_ball_normE`
  + global instances `Proper_nbhs'_numFieldType`, `Proper_nbhs'_realType`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pseudoMetricNormedZmodType`, `normedModType`.
  + module `numFieldNormedType` with an `Exports` submodule
    * many canonicals and coercions
    * exports `Export numFieldTopology.Exports`
  + canonical `R_regular_completeType`, `R_regular_CompleteNormedModule`

### Changed

- in `ereal.v`:
  + generalize lemma `lee_sum_nneg_subfset`
- in `sequences.v`:
  + generalize lemmas `ereal_nondecreasing_series`, `is_cvg_ereal_nneg_series`,
    `ereal_nneg_series_lim_ge0`, `ereal_nneg_series_pinfty`
- in `measure.v`:
  + generalize lemma `bigUB_of`
  + generalize theorem `Boole_inequality`
- in `classical_sets.v`:
  + `bigcup_distrr`, `bigcup_distrl` generalized

### Renamed

- canonicals and coercions have been changed so that there is not need
  anymore for explicit types casts to `R^o`, `[filteredType R^o of R^o]`,
  `[filteredType R^o * R^o of R^o * R^o]`, `[lmodType R of R^o]`,
  `[normedModType R of R^o]`,`[topologicalType of R^o]`, `[pseudoMetricType R of R^o]`

- `topology.v` now imports `reals`
- `normedtype.v` now imports `vector`, `fieldext`, `falgebra`,
  `numFieldTopology.Exports`
- `derive.v` now imports `numFieldNormedType.Exports`
- `sequences.v` now imports `numFieldNormedType.Exports`

### Renamed

### Removed

- in `topology.v`:
  + section `numFieldType_canonical`
- in `normedtype.v`:
  + lemma `R_ball`
  + definition `numFieldType_pseudoMetricNormedZmodMixin`
  + canonical `numFieldType_pseudoMetricNormedZmodType`
  + global instance `Proper_nbhs'_realType`
  + lemma `R_normZ`
  + definition `numFieldType_NormedModMixin`
  + canonical `numFieldType_normedModType`

### Infrastructure

### Misc
