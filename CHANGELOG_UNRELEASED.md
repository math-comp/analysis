# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

- in `functions.v`:
  + `addrfunE` renamed to `addrfctE` and generalized to `Type`, `zmodType`
  + `opprfunE` renamed to `opprfctE` and generalized to `Type`, `zmodType`
- moved from `functions.v` to `classical_sets.v`
  + lemma `subsetW`, definition `subsetCW`
- in `mathcomp_extra.v`:
  + fix notation `ltLHS`

### Renamed

- in `topology.v`:
  + `open_bigU` -> `bigcup_open`
- in `functions.v`:
  + `mulrfunE` -> `mulrfctE`
  + `scalrfunE` -> `scalrfctE`
  + `exprfunE` -> `exprfctE`
  + `valLr` -> `valR`
  + `valLr_fun` -> `valR_fun`
  + `valLrK` -> `valRK`
  + `oinv_valLr` -> `oinv_valR`
  + `valLr_inj_subproof` -> `valR_inj_subproof`
  + `valLr_surj_subproof` -> `valR_surj_subproof`

### Removed

### Infrastructure

### Misc
