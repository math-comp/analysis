# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal_normedtype.v`:
  + lemma `ge0_cvgMly`

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

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
