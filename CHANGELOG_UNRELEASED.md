# Changelog (unreleased)

## [Unreleased]

### Added
- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

- in `tvs.v`
  + lemmas `cvg_sum`, `sum_continuous`

- in `unstable.v`:
  + structure `Norm`
  + lemmas `normMn`, `normN`, `ler_norm_sum`
  + definitions `max_norm`, `max_space`
  + lemmas `max_norm_ge0`, `le_coord_max_norm`, `max_norm0`, `ler_max_normD`,
    `max_norm0_eq0`, `max_normZ`, `max_normMn`, `max_normN`

- in `normed_module.v`:
  + structure `NormedVector`
  + definition `normedVectType`
  + lemmas `sup_closed_ball_compact`, `equivalence_norms`,
    `linear_findim_continuous`

### Changed
- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

### Renamed
- in set_interval.v
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
