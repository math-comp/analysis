# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal_normedtype.v`:
  + lemma `ge0_cvgMly`

- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in file `nat_topology.v`,
  + new lemma `near_infty_after`.
- in file `num_topology.v`,
  + new lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, and `at_right_shift`.

- in file `normed_module.v`,
  + new lemmas `cvg1MC`, `cvg1M`, `cvgCM1`, `cvgM1`, `cvg0MC`, `cvg0M`, 
    `cvgCM0`, and `cvgM0`.
- in file `pseudometric_normed_Zmodule.v`,
  + new lemmas `cvgDl`, `cvgDr`, `cvgBl`, `cvgBr`, `cvg0D`, `cvg0DC`, 
    `cvgD0`, `cvgCD0`, `cvg0B`, `cvg0BC`, `cvgB0`, `cvgCB0`, and `cvgN0`.

- in `derive.v`
  + new lemmas `derive1Dn`, `der1_scaleLR`, `deriveZLR`, `derivableZLR`, 
    `derivable_shiftf`, `derive_shiftf`, `is_derive_shiftf`, `derive1_shiftf`, 
    `near_eq_derive1n_near`, `near_eq_derive1_near`, `near_eq_derive1n`, and 
    `near_eq_derive1`.

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)

- moved from `realfun.v` to `derive.v`: 
  + lemmas `is_deriveV`, `is_derive1_comp`.
- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
