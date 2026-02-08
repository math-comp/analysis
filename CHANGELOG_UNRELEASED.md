# Changelog (unreleased)

## [Unreleased]

### Added
- in order_topology.v
  + lemma `itv_closed_ends_closed`
- in classical_sets.v
  + lemma `in_set1_eq`

- in set_interval.v
  + definitions `itv_is_closed_unbounded`, `itv_is_cc`, `itv_closed_ends`

- in `Rstruct.v`:
  + lemmas `R0E` and `R1E`
  + multirule `RealsE` to convert from Stdlib reals to Analysis ones

- in `Rstruct_topology.v`:
  + lemma `RlnE`
- in probability.v
  + lemma `pmf_ge0`
  + lemmas `pmf_gt0_countable`, `pmf_measurable`

### Changed
- in set_interval.v
  + `itv_is_closed_unbounded` (fix the definition)

- in set_interval.v
  + `itv_is_open_unbounded`, `itv_is_oo`, `itv_open_ends` (Prop to bool)

- in `lebesgue_Rintegrable.v`:
  + lemma `Rintegral_cst` (does not use `cst` anymore)

### Renamed
- in `set_interval.v`:
  + `itv_is_ray` -> `itv_is_open_unbounded`
  + `itv_is_bd_open` -> `itv_is_oo`

- `weak_topology.v` -> `initial_topology.v`
  + `weak_topology` -> `initial_topology`
  + `weak_continuous` -> `initial_continuous`
  + `weak_ent` -> `initial_ent`
  + `weak_ball` -> `initial_ball`
  + `weak_ballE` -> `initial_ballE`
  + `open_order_weak` -> `open_order_initial`
  + `continuous_comp_weak` -> `continuous_comp_initial`

- in `one_point_compactification.v`:
  + `one_point_compactification_weak_topology` ->
    `one_point_compactification_initial_topology`

- in `subspace_topology.v`:
  + `weak_subspace_open` -> `initial_subspace_open`

- in `functions_spaces.v`:
  + `weak_sep_cvg` -> `initial_sep_cvg`
  + `weak_sep_nbhsE` -> `initial_sep_nbhsE`
  + `weak_sep_openE` -> `initial_sep_openE`
  + `join_product_weak` -> `join_product_initial`

### Generalized

### Deprecated

### Removed

- in `weak_topology.v`:
  + lemmas `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`,
    `weak_ent_split`, `weak_ent_nbhs`, `weak_pseudo_metric_ball_center`,
    `weak_pseudo_metric_entourageE`
    (now `Let`'s in `initial_topology.v`)

### Infrastructure

### Misc
