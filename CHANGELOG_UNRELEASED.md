# Changelog (unreleased)

## [Unreleased]

### Added

- in file `normedtype.v`:
  + definition `bigcup_ointsub`
  + lemmas `bigcup_ointsub0`, `open_bigcup_ointsub`, `is_interval_bigcup_ointsub`,
    `bigcup_ointsub_sub`, `open_bigcup_rat`
- in file `lebesgue_measure.v`:
  + lemmas `is_interval_measurable`, `open_measurable`, `continuous_measurable_fun`
- in `classical_sets.v`:
  + lemma `preimage_setT`
- in `ereal.v`:
  + definition `expe` with notation `^+`
  + definition `enatmul` with notation `*+` (scope `%E`)
  + definition `ednatmul` with notation `*+` (scope `%dE`)
  + lemmas `fineM`, `enatmul_pinfty`, `enatmul_ninfty`, `EFin_natmul`, `mule2n`, `expe2`,
    `mule_natl`
  + lemmas `ednatmul_pinfty`, `ednatmul_ninfty`, `EFin_dnatmul`, `dmule2n`, `ednatmulE`,
    `dmule_natl`
- in `esum.v`:
  + lemma `esum_set1`
- in `ereal.v`:
  + lemmas `oppeB`, `doppeB`, `fineB`, `dfineB`

### Changed

- in `esumv`:
  + remove one hypothesis in lemmas `reindex_esum`, `esum_image`

### Renamed

- in `ereal.v`:
  + `num_abs_le` -> `num_abse_le`
  + `num_abs_lt` -> `num_abse_lt`

### Removed

### Infrastructure

### Misc
