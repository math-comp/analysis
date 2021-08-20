# Changelog (unreleased)

## [Unreleased]

### Added

- in `boolp.v`:
  + lemmas `orA`, `andA`
- in `measure.v`:
  + definition `seqDU`
  + lemmas `trivIset_seqDU`, `bigsetU_seqDU`, `seqDU_bigcup_eq`, `seqDUE`

### Changed

- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`

- in `ereal.v`:
  + lemmas `ge0_adde_def`, `onee_neq0`, `mule0`, `mul0e`
  + lemmas `mulrEDr`, `mulrEDl`, `ge0_muleDr`, `ge0_muleDl`
  + lemmas `ge0_sume_distrl`, `ge0_sume_distrr`
  + lemmas `mulEFin`, `mule_neq0`, `mule_ge0`, `muleA`
  + lemma `muleE`
  + lemmas `muleN`, `mulNe`, `muleNN`, `gee_pmull`, `lee_mul01Pr`
  + lemmas `lte_pdivr_mull`, `lte_pdivr_mulr`, `lte_pdivl_mull`, `lte_pdivl_mulr`,
    `lte_ndivl_mulr`, `lte_ndivl_mull`, `lte_ndivr_mull`, `lte_ndivr_mulr`
  + lemmas `lee_pdivr_mull`, `lee_pdivr_mulr`, `lee_pdivl_mull`, `lee_pdivl_mulr`,
    `lee_ndivl_mulr`, `lee_ndivl_mull`, `lee_ndivr_mull`, `lee_ndivr_mulr`
  + lemmas `mulrpinfty`, `mulrninfty`, `mule_gt0`
- in `normedtype.v`:
  + lemma `mule_continuous`

### Changed

- in `ereal.v`:
  + change definition `mule` such that 0 x oo = 0
  + `adde` now defined using `nosimpl` and `adde_def`

### Renamed

- in `ereal.v`:
  + `adde` -> `adde_def`
  + `adde_def` -> `adde_defined`
  + `adde_defC` -> `adde_definedC`
  + `ge0_adde_def`-> `ge0_adde_defined`
  + `fin_num_adde_def` -> `fin_num_adde_defined`
  + `adde_def_nneg_series` -> `adde_defined_nneg_series`

### Removed

- in `boolp.v`:
  + definition `PredType`
  + local notation `predOfType`

### Infrastructure

### Misc
