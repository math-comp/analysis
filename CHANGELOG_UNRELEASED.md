# Changelog (unreleased)

## [Unreleased]

### Added

- in `lebesgue_stieltjes_measure.v`:
  + `sigma_finite_measure` HB instance on `lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + `sigma_finite_measure` HB instance on `lebesgue_measure`

- in `lebesgue_integral.v`:
  + `sigma_finite_measure` instance on product measure `\x`

### Changed
  

- in `normedtype.v`:
  + lemmas `vitali_lemma_finite` and `vitali_lemma_finite_cover` now returns
    duplicate-free lists of indices

- moved from `lebesgue_integral.v` to `measure.v`:
  + definition `ae_eq`
  + lemmas
	`ae_eq0`,
	`ae_eq_comp`,
	`ae_eq_funeposneg`,
	`ae_eq_refl`,
	`ae_eq_trans`,
	`ae_eq_sub`,
	`ae_eq_mul2r`,
	`ae_eq_mul2l`,
	`ae_eq_mul1l`,
	`ae_eq_abse`

- in `topology.v`:
  + lemmas `nbhsx_ballx` and `near_ball` take a parameter of type `R` instead of `{posnum R}`

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
