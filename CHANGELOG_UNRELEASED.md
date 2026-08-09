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
- in `esum.v`:
  + lemmas `pos_esum_ge1`, `le_pos_esum_fine`, `sum_esum_ge`, `le_esum_fine`,
    `subset_esum`, `esum0`, `esum_if_eq_op_set1`, `esum_neq0`, `esum_ge1`
  + lemmas `eq_esummable`, `le_esummable`, `esummableZl`, `esummableZr`,
    `esummableMl`, `esummableMr`, `esummableM`
  + lemmas `esummable_esum_funepos`, `esummable_esum_funeneg`,
     `esummable_esum_fin_num`, `esummable_esumN`
  + lemma `esumE`
  + lemmas `esummable_esumZ`, `esummable_esumD`, `esummableB`

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

### Renamed

- in `esum.v`:
  + `summable` -> `esummable`
  + `summable_pinfty` -> `esummable_pinfty`
  + `summableE` -> `esummableE`
  + `summableD` -> `esummableD`
  + `summableN` -> `esummableN`
  + `summableB` -> `esummableB`
  + `summable_funepos` -> `esummable_funepos`
  + `summable_funeneg` -> `esummable_funeneg`
  + `summable_fine_sum` -> `esummable_fine_sum`
  + `summable_cvg` -> `esummable_cvg`
  + `summable_nneseries_lim` -> `esummable_nneseries_lim`
  + `summable_eseries` -> `esummable_eseries`
  + `summable_eseries_esum` -> `esummable_eseries_esum`

- in `lebesgue_integrable.v`:
  + `integrable_summable` -> `integrable_esummable`

- in `lebesgue_integral_nonneg.v`:
  + `summable_integral_dirac` -> `esummable_integral_dirac`

### Generalized

- in `esum.v`:
  + lemmma `le_esum`

### Deprecated

### Removed

### Infrastructure

### Misc
