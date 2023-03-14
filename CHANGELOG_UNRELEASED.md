# Changelog (unreleased)

## [Unreleased]

### Added

- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_itv`

### Changed

### Renamed

- in `lebesgue_measure.v`:
  + `punct_eitv_bnd_pinfty` -> `punct_eitv_bndy`
  + `punct_eitv_ninfty_bnd` -> `punct_eitv_Nybnd`
  + `eset1_pinfty` -> `eset1y`
  + `eset1_ninfty` -> `eset1Ny`
  + `ErealGenOInfty.measurable_set1_ninfty` -> `ErealGenOInfty.measurable_set1Ny`
  + `ErealGenOInfty.measurable_set1_pinfty` -> `ErealGenOInfty.measurable_set1y`
  + `ErealGenCInfty.measurable_set1_ninfty` -> `ErealGenCInfty.measurable_set1Ny`
  + `ErealGenCInfty.measurable_set1_pinfty` -> `ErealGenCInfty.measurable_set1y`

- in `set_interval.v`:
  + `conv` -> `line_path`
  + `conv_id` -> `line_path_id`
  + `ndconv` -> `ndline_path`
  + `convEl` -> `line_pathEl`
  + `convEr` -> `line_pathEr`
  + `conv10` -> `line_path10`
  + `conv0` -> `line_path0`
  + `conv1` -> `line_path1`
  + `conv_sym` -> `line_path_sym`
  + `conv_flat` -> `line_path_flat`
  + `leW_conv` -> `leW_line_path`
  + `convK` -> `line_pathK`
  + `conv_inj` -> `line_path_inj`
  + `conv_bij` -> `line_path_bij`

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemmas `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd`
    (use `emeasurable_itv` instead)

### Removed

### Infrastructure

### Misc
