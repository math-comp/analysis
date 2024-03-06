# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`
  + lemma `ln_lt0`

- in `lebesgue_integral.v`
  + lemma `ge0_integralZr`

### Changed

- move from `kernel.v` to `measure.v`
  + definition `mset`, `pset`, `pprobability`
  + lemmas `lt0_mset`, `gt1_mset`

- in `measure.v`:
  + lemma `sigma_finiteP` generalized to an equivalence and changed to use `[/\ ..., .. & ....]`

### Renamed

- in `constructive_ereal.v`:
  + `lee_addl` -> `leeDl`
  + `lee_addr` -> `leeDr`
  + `lee_add2l` -> `leeD2l`
  + `lee_add2r` -> `leeD2r`
  + `lee_add` -> `leeD`
  + `lee_sub` -> `leeB`
  + `lee_add2lE` -> `leeD2lE`
  + `lte_add2lE` -> `lteD2lE`
  + `lee_oppl` -> `leeNl`
  + `lee_oppr` -> `leeNr`
  + `lte_oppr` -> `lteNr`
  + `lte_oppl` -> `lteNl`
  + `lte_add` -> `lteD`
  + `lte_addl` -> `lteDl`
  + `lte_addr` -> `lteDr`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
