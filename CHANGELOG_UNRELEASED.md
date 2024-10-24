# Changelog (unreleased)

## [Unreleased]

### Added

- new directory `theories/topology` with new files:
  + `topology.v`
  + `bool_topology.v`
  + `compact.v`
  + `connected.v`
  + `matrix_topology.v`
  + `nat_topology.v`
  + `order_topology.v`
  + `product_topology.v`
  + `pseudometric_structure.v`
  + `subspace_topology.v`
  + `supremum_topology.v`
  + `topology_structure.v`
  + `uniform_structure.v`
  + `weak_topology.v`
  + `num_topology.v`
  + `quotient_topology.v`

### Changed

- The file `topology.v` has been split into several files in the directory 
  `topology_theory`. Unless stated otherwise, definitions, lemmas, etc. 
  have been moved without changes. The same import will work as before, 
  `Require Import topology.v`.

- in `matrix_topology.v` (new file):
  + lemmas `mx_ball_center`, `mx_ball_sym`, `mx_ball_triangle`, `mx_entourage`
    are now `Local`

- in `weak_topology.v` (new file):
  + lemmas `wopT`, `wopI`, `wop_bigU` are now `Local`

- in `supremum_topology.v` (new file):
  + lemmas `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
    `sup_ent_nbhs` are now `Local`

- The function `map_pair` was moved from `topology.v` to `mathcomp_extra.v`.
- in `forms.v`:
  + notation `'e_`

- in `lebesgue_integral.v`:
  + notation `\x`

### Renamed

### Generalized

- in `num_topology.v` (new file):
  + lemma `nbhs0_lt` generalized from `realType` to `realFieldType`

### Deprecated

- in `pseudometric_structure.v` (new file):
  + definition `cvg_toi_locally` (use `cvgi_ballP` instead)

### Removed

- file `topology.v` (contents now in directory `topology`)

### Infrastructure

### Misc
