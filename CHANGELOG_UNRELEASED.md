# Changelog (unreleased)

## [Unreleased]

### Added

- in `boolp.v`, lemmas for classical reasoning `existsNP`, `existsPN`,
  `forallNP`, `forallPN`, `Nimply`, `orC`.
- in `classical_sets.v`, definitions for supremums: `ul`, `lb`,
  `supremum`
- in `ereal.v`:
  + technical lemmas `lee_ninfty_eq`, `lee_pinfty_eq`, `lte_subl_addr`
  + lemmas about supremum: `ereal_supremums_neq0`
  + definitions:
    * `ereal_sup`, `ereal_inf`
  + lemmas about `ereal_sup`:
    * `ereal_sup_ub`, `ub_ereal_sup`, `ub_ereal_sup_adherent`
- in `normedtype.v`:
  + function `contract` (bijection from `{ereal R}` to `R`)
  + `ereal_pseudoMetricType R`

### Changed

- in `reals.v`, `pred` replaced by `set` from `classical_sets.v`
  + change propagated in many files

### Renamed

### Removed

### Infrastructure

### Misc
