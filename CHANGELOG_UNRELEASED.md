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
- in `realfun.v`:
  + lemmas `cvge_pinftyP`, `nonincreasing_cvge`

- in `probability.v`:
  + definition `cdf`
  + lemmas `cdf_ge0`, `cdf_le1`, `cdf_nondecreasing`, `cdf_cvgr1_pinfty`, `cdf_cvg0_ninfty`

### Changed

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package

### Renamed

### Generalized

### Deprecated

### Removed

- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)

### Infrastructure

### Misc
