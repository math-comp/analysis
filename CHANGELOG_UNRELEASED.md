# Changelog (unreleased)

## [Unreleased]

### Added
- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

### Changed
- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

- in `functions.v`:
  + lemmas `fun_maxC`, `fun_minC`, `min_fun_to_max`, `max_fun_to_min`

- in `derive.v`:
  + lemmas `derivable_max`, `derive_maxl`, `derive_maxr` `derivable_min`, `derive_minl`, `derive_minr`

### Renamed
- in set_interval.v
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
