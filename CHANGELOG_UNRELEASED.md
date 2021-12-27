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

### Changed

- in `topology.v`:
  + renamed and generalized `setC_subset_set1C` implication to
    equivalence `subsetC1`
- notation `\*` moved from `realseq.v` to `topology.v`

### Renamed

- in `topology.v:
  + `hausdorff` -> `hausdorff_space`

### Removed

- in `realseq.v`:
  + notation `\-`

### Infrastructure

### Misc
