# Changelog (unreleased)

## [Unreleased]

### Added

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvg0D`, `cvgD0`, `cvg0B`, `cvgB0`, `cvgN0`

- in `normed_module.v`:
  + lemmas `cvg1M`, `cvgM1`, `cvg0M`, `cvgM0`
  + lemmas `cvg1Z`, `cvg0Z`, `cvgZ0`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_leq`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`,
    `at_left_shift`, `at_right_shift`

- in `num_normedtype.v`,
  + lemmas `pinftyV`, `ninftyV`, `cvgryV`, `cvgrNyV`, `lt0_cvgMlNy`, 
    `lt0_cvgMrNy`, `lt0_cvgMly`, `lt0_cvgMry`

- in `pseudometric_normed_Zmodule.v`,
  + lemmas `fmap_at_left0P`, `fmap_at_right0E`

- in `tvs.v`,
  + lemmas `near_shiftE`, `nearZE`

- in `num_topology.v`:
  + lemmas `near_right_in_itv`, `near_left_in_itv`

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`

### Renamed

### Generalized

- in `tvs.v`:
  + lemma `nbhsB`

### Deprecated

### Removed

### Infrastructure

### Misc
