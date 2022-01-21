# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + definitions `kolmogorov_space`, `accessible_space`
  + lemmas `accessible_closed_set1`, `accessible_kolmogorov`
- in `ereal.v`:
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

### Changed

- in `topology.v`:
  + renamed and generalized `setC_subset_set1C` implication to
    equivalence `subsetC1`
- in `ereal.v`:
  + lemmas `ereal_sup_gt`, `ereal_inf_lt` now use `exists2`
- notation `\*` moved from `realseq.v` to `topology.v`

### Renamed

- in `topology.v:
  + `hausdorff` -> `hausdorff_space`

### Removed

- in `realseq.v`:
  + notation `\-`

### Infrastructure

- add `.dir-locals.el` for company-coq symbols

### Misc
