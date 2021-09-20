# Changelog (unreleased)

## [Unreleased]

### Added

- in `boolp.v`:
  + lemmas `orA`, `andA`
- in `measure.v`:
  + definition `seqDU`
  + lemmas `trivIset_seqDU`, `bigsetU_seqDU`, `seqDU_bigcup_eq`, `seqDUE`
- in `ereal.v`:
  + notation `x +? y` for `adde_def x y`
- in `sequences.v`:
  + lemmas `lt_lim`, `nondecreasing_dvg_lt`, `ereal_lim_sum`
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
  + lemmas `mulrpinfty`, `mulrninfty`, `mulpinftyr`, `mulninftyr`, `mule_gt0`
  + definition `mulrinfty`
  + lemmas `mulN1e`, `muleN1`
  + lemmas `mule_ninfty_pinfty`, `mule_pinfty_ninfty`, `mule_pinfty_pinfty`
  + lemmas `mule_le0_ge0`, `mule_ge0_le0`, `pmule_rle0`, `pmule_lle0`,
    `nmule_lle0`, `nmule_rle0`
  + lemma `sube0`
- in `normedtype.v`:
  + lemma `mule_continuous`
- in `cardinality.v`:
  + definition `nat_of_pair`, lemma `nat_of_pair_inj`

### Changed

- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`
- in `ereal.v`:
  + change definition `mule` such that 0 x oo = 0
  + `adde` now defined using `nosimpl` and `adde_subdef`
  + `mule` now defined using `nosimpl` and `mule_subdef`
- in `real.v`:
  + generalize from `realType` to `realDomainType` lemmas
    `has_ub_image_norm`, `has_inf_supN`
- in `sequences.v`:
  + generalize from `realType` to `realFieldType` lemmas
    `cvg_has_ub`, `cvg_has_sup`, `cvg_has_inf`
- in `sequences.v`:
  + change the statements of `cvgPpinfty`, `cvgPminfty`,
    `cvgPpinfty_lt`
- in `sequences.v`:
  + generalize `nondecreasing_seqP`, `nonincreasing_seqP`, `increasing_seqP`,
    `decreasing_seqP` to equivalences
  + generalize `lee_lim`, `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`,
    `ereal_cvgD`, `ereal_limD`, `ereal_pseries0`, `eq_ereal_pseries` from `realType` to `realFieldType`

### Renamed

- in `ereal.v`:
  + `adde` -> `adde_subdef`
  + `mule` -> `mule_subdef`

### Removed

- in `boolp.v`:
  + definition `PredType`
  + local notation `predOfType`

### Infrastructure

### Misc
