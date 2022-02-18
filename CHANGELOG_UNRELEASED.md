# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal.v`:
  + lemmas `esum_ninftyP`, `esum_pinftyP`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinftyP`, `desum_ninftyP`
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`
- in `ereal.v`:
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`
- in `ereal.v`:
  + lemmas `mule_def_fin`, `mule_def_neq0_infty`, `mule_def_infty_neq0`, `neq0_mule_def`
  + notation `\-` in `ereal_scope` and `ereal_dual_scope`
  + lemma `fin_numB`
  + lemmas `mule_eq_pinfty`, `mule_eq_ninfty`
  + lemmas `fine_eq0`, `abse_eq0`
- in `topology.v`:
  + lemma `filter_pair_set`
- in `topology.v`:
  + definition `prod_topo_apply`
  + lemmas `prod_topo_applyE`, `prod_topo_apply_continuous`, `hausdorff_product`
- in `topology.v`:
  + `closedC` renamed `open_closedC`
  + `openC` renamed `closed_openC`
- in `topology.v`:
  + lemmas `closedC`, `openC` 
  + notation `'{within A, continuous f}`
  + lemmas `continuous_subspace_in`
  + lemmas`closed_subspaceP`, `closed_subspaceW`, `closure_subspaceW`
  + lemmas `nbhs_subspace_subset`, `continuous_subspaceW`, `nbhs_subspaceT`,
    `continuous_subspaceT_for`, `continuous_subspaceT`, `continuous_open_subspace`
  + globals `subspace_filter`, `subspace_proper_filter`
  + notation `{within ..., continuous ...}`
- in `derive.v`
  + lemma `MVT_segment`
- in `normedtype.v`
  + generalize `IVT` with subspace topology
- in `realfun.v`:
  + lemma `continuous_subspace_itv`

### Changed

- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`

### Renamed

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`

- in `topology.v`:
  + generalize `connected_continuous_connected`, `continuous_compact`
  + arguments of `subspace`
- in `derive.v`:
  + generalize `EVT_max`, `EVT_min`, `Rolle`, `MVT`, `ler0_derive1_nincr`,
    `le0r_derive1_ndecr` with subspace topology
  + implicits of `cvg_at_rightE`, `cvg_at_leftE`

### Renamed

- in `topology.v`:
  + `closedC` -> `open_closedC`
  + `openC` -> `closed_openC`

### Removed

### Infrastructure

### Misc
