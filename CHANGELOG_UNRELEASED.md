# Changelog (unreleased)

## [Unreleased]

### Added

- in `cardinality.v`:
  + lemma `infinite_setD`

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

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
