# Changelog (unreleased)

## [Unreleased]

### Added

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvg0D`, `cvgD0`, `cvg0B`, `cvgB0`, `cvgN0`

- in `normed_module.v`:
  + lemmas `cvg1M`, `cvgM1`, `cvg0M`, `cvgM0`
  + lemmas `cvg1Z`, `cvg0Z`, `cvgZ0`

- in `normal_distribution.v`:
  + definition `post_stddev`
  + lemmas `post_stddev_gt0`, `post_stddevE`
  + definition `post_mean`
  + lemmas `normal_fun_conjugate`, `normal_pdf_conjugate`, `normal_prob_conjugate`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_leq`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`,
    `at_left_shift`, `at_right_shift`

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
