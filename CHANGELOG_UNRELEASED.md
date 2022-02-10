# Changelog (unreleased)

  in `trigo.v`, the `realType` argument of `pi` is implicit
  in `trigo.v`, the printed type of `acos`, `asin`, `atan` is `R -> R`

## [Unreleased]

### Added

- in `ereal.v`:
  + lemmas `esum_ninfty`, `esum_pinfty`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinfty`, `desum_ninfty`

### Changed

### Renamed

- in `ereal.v`:
  + `esum_pinfty` -> `esum_ord_pinfty`
  + `esum_ninfty` -> `esum_ord_ninfty`
  + `desum_pinfty` -> `desum_ord_pinfty`
  + `desum_ninfty` -> `desum_ord_ninfty`

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`

### Infrastructure

### Misc
