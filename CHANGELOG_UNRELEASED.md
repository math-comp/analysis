# Changelog (unreleased)

## [Unreleased]

### Added
- in `normedtype.v`:
  + lemma `le_closed_ball` 
- in `sequences.v`:
  + theorem `Baire`
  + definition `bounded_fun_norm`
  + lemma `bounded_landau`
  + definition `pointwise_bounded`
  + definition `uniform_bounded`
  + theorem `Banach_Steinhauss`

- in `ereal.v`:
  + lemmas `esum_ninftyP`, `esum_pinftyP`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinftyP`, `desum_ninftyP`

### Changed

- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`

### Renamed

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`

### Infrastructure

### Misc
