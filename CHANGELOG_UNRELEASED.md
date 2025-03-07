# Changelog (unreleased)

## [Unreleased]

### Added

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- file `constructive_ereal.v`:
  + definition `iter_mule`
  + lemma `prodEFin`

- file `exp.v`:
  + lemma `expR_sum`

- file `lebesgue_integral.v`:
  + lemma `measurable_fun_le`

### Changed

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package

### Renamed

- in `lebesgue_integral.v`:
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`

### Generalized

- in `constructive_ereal.v`:
  + lemma `EFin_natmul`

### Deprecated

### Removed

- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)

### Infrastructure

### Misc
