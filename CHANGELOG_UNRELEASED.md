# Changelog (unreleased)

## [Unreleased]

### Added

- new directory `theories/topology` with new files:
  + `all_topology.v`
  + `bool_topology.v`
  + `compact.v`
  + `connected.v`
  + `matrix_topology.v`
  + `nat_topology.v`
  + `order_topology.v`
  + `product_topology.v`
  + `pseudometric_mixin.v`
  + `subspace_topology.v`
  + `supremum_topology.v`
  + `topology_mixin.v`
  + `uniform_mixin.v`
  + `weak_topology.v`
  + `num_topology.v`
  + `quotient_topology.v`

### Changed

- The file `topology.v` has been split into several files in the directory `topology`.
  Unless stated otherwise, definitions, lemmas, etc. have been moved without changes,
  we expect the user to recover them by `Require Import all_topology.v`.

- in `matrix_topology.v` (new file):
  + lemmas `mx_ball_center`, `mx_ball_sym`, `mx_ball_triangle`, `mx_entourage`
    are now `Local`

- in `weak_topology.v` (new file):
  + lemmas `wopT`, `wopI`, `wop_bigU` are now `Local`

- in `supremum_topology.v` (new file):
  + lemmas `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
    `sup_ent_nbhs` are now `Local`

- Th function `map_pair` was moved from `topology.v` to `mathcomp_extras.v`.

### Renamed

### Generalized

- in `num_topology.v` (new file):
  + lemma `nbhs0_lt` generalized from `realType` to `realFieldType`

### Deprecated

- in `pseudometric_mixin.v` (new file):
  + definition `cvg_toi_locally` (use `cvgi_ballP` instead)

### Removed

- file `topology.v` (contents now in directory `topology`)

### Infrastructure

### Misc
