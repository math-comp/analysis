# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `setDIr`
  + lemmas `setMT`, `setTM`, `setMI`
  + lemmas `setSM`, `setM_bigcupr`, `setM_bigcupl`
- in `ereal.v`:
  + lemma `onee_eq0`
  + lemma `EFinB`
  + lemmas `mule_eq0`, `mule_lt0_lt0`, `mule_gt0_lt0`, `mule_lt0_gt0`,
    `pmule_rge0`, `pmule_lge0`, `nmule_lge0`, `nmule_rge0`,
    `pmule_rgt0`, `pmule_lgt0`, `nmule_lgt0`, `nmule_rgt0`,
- in `measure.v`:
  + hints for `measurable0` and `measurableT`

### Changed

- in `normedtype.v`:
  + `nbhs_minfty_lt` renamed to `nbhs_ninfty_lt_pos` and changed to not use `{posnum R}`
  + `nbhs_minfty_le` renamed to `nbhs_ninfty_le_pos` and changed to not use `{posnum R}`
- in `sequences.v`:
  + lemma `is_cvg_ereal_nneg_natsum`: remove superfluous `P` parameter

### Renamed

- in `normedtype.v`:
  + `nbhs_minfty_lt_real` -> `nbhs_ninfty_lt`
  + `nbhs_minfty_le_real` -> `nbhs_ninfty_le`
- in `sequences.v`:
  + `cvgNminfty` -> `cvgNninfty`
  + `cvgPminfty` -> `cvgPninfty`
  + `ler_cvg_minfty` -> `ler_cvg_ninfty`
- in `normedtype.v`:
  + `nbhs_pinfty_gt` -> `nbhs_pinfty_gt_pos`
  + `nbhs_pinfty_ge` -> `nbhs_pinfty_ge_pos`
  + `nbhs_pinfty_gt_real` -> `nbhs_pinfty_gt`
  + `nbhs_pinfty_ge_real` -> `nbhs_pinfty_ge`
- in `measure.v`:
  + `measure_bigcup` -> `measure_bigsetU`
- in `ereal.v`:
  + `mulrEDr` -> `muleDr`
  + `mulrEDl` -> `muleDl`
  + `dmulrEDr` -> `dmuleDr`
  + `dmulrEDl` -> `dmuleDl`
  + `NEFin` -> `EFinN`
  + `addEFin` -> `EFinD`
  + `mulEFun` -> `EFinM`
  + `daddEFin` -> `dEFinD`
  + `dsubEFin` -> `dEFinB`
- in `normedtype.v`:
  + lemmas `bounded_fun_has_ubound`, `bounded_funN`, `bounded_fun_has_lbound`,
    `bounded_funD`
- in `reals.v`:
  + lemma `has_ub_lbN`
- in `sequences.v`:
  + lemma `ereal_is_cvgD`

### Changed

- in `sequences.v`:
  + statements of lemmas `nondecreasing_cvg`, `nondecreasing_is_cvg`,
    `nonincreasing_cvg`, `nonincreasing_is_cvg` use `has_{l,u}bound`
    predicates instead of requiring an additional variable
  + statement of lemma `S1_sup` use `ubound` instead of requiring an
    additional variable

### Renamed

- in `sequences.v`:
  + `nondecreasing_seq_ereal_cvg` -> `ereal_nondecreasing_cvg`

### Removed

### Infrastructure

### Misc
