# Changelog (unreleased)

## [Unreleased]

### Added
- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

- in `Rstruct_topology.v`:
  + lemma `RlnE`

### Changed
- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

- in `lebesgue_Rintegrable.v`:
  + lemma `Rintegral_cst` (does not use `cst` anymore)

### Renamed
- in set_interval.v
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
