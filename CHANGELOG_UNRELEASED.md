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
- in `normedtypes.v`:
  + lemma `is_intervalPlt`
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
- in `topology.v`
  + lemma `le_bigmax`
- in `real.v`:
  + lemmas `floor1`, `floor_neq0`
- in `sequences.v`:
  + lemmas `ereal_nondecreasing_opp`, `ereal_nondecreasing_is_cvg`, `ereal_nonincreasing_cvg`,
    `ereal_nonincreasing_is_cvg`
- in `normedtype.v`:
  + lemmas `ereal_is_cvgN`, `ereal_cvgZr`, `ereal_is_cvgZr`, `ereal_cvgZl`, `ereal_is_cvgZl`,
    `ereal_limZr`, `ereal_limZl`, `ereal_limN`

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
- in `topology.v`:
  + replace `closed_cvg_loc` and `closed_cvg` by a more general lemma `closed_cvg`
- move from `sequences.v` to `normedtype.v` and generalize from `nat` to `T : topologicalType`
  + lemmas `ereal_cvgN`
- in `normedtype.v`:
  + definition `is_interval`
- in `ereal.v`:
  + lemmas `lte_addl`, `lte_subl_addr`, `lte_subl_addl`, `lte_subr_addr`,
    `lte_subr_addr`, `lte_subr_addr`, `lb_ereal_inf_adherent`
- in `sequences.v`:
  + lemma `ereal_pseries_pred0` moved from `csum.v`, minor generalization

### Renamed
- in `classical_sets.v`:
  + generalize lemma `perm_eq_trivIset`

- in `ereal.v`:
  + `adde` -> `adde_subdef`
  + `mule` -> `mule_subdef`
- in `normedtype.v`:
  the following lemmas have been generalized to `orderType`,
  renamed as follows, moved out of the module `BigmaxBigminr`
  to `topology.v`:
  + `bigmaxr_mkcond` -> `bigmax_mkcond`
  + `bigmaxr_split` -> `bigmax_split`
  + `bigmaxr_idl` -> `bigmax_idl`
  + `bigmaxrID` -> `bigmaxID`
  + `bigmaxr_seq1` -> `bigmax_seq1`
  + `bigmaxr_pred1_eq` -> `bigmax_pred1_eq`
  + `bigmaxr_pred1` -> `bigmax_pred1`
  + `bigmaxrD1` -> `bigmaxD1`
  + `ler_bigmaxr_cond`  -> `ler_bigmax_cond `
  + `ler_bigmaxr` -> `ler_bigmax`
  + `bigmaxr_lerP` -> `bigmax_lerP`
  + `bigmaxr_sup` -> `bigmax_sup`
  + `bigmaxr_ltrP` -> `bigmax_ltrP`
  + `bigmaxr_gerP` -> `bigmax_gerP`
  + `bigmaxr_eq_arg` -> `bigmax_eq_arg`
  + `bigmaxr_gtrP` -> `bigmax_gtrP`
  + `eq_bigmaxr` -> `eq_bigmax`
- in `normedtype.v`:
  * module `BigmaxBigminr` -> `Bigminr`
- in `sequences.v`:
  + `nondecreasing_seq_ereal_cvg` -> `nondecreasing_ereal_cvg`

### Removed

- in `boolp.v`:
  + definition `PredType`
  + local notation `predOfType`
- in `nngnum.v`:
  + module `BigmaxrNonneg` containing the following lemmas:
    * `bigmaxr_mkcond`, `bigmaxr_split`, `bigmaxr_idl`, `bigmaxrID`,
      `bigmaxr_seq1`, `bigmaxr_pred1_eq`, `bigmaxr_pred1`, `bigmaxrD1`,
      `ler_bigmaxr_cond`, `ler_bigmaxr`, `bigmaxr_lerP`, `bigmaxr_sup`,
      `bigmaxr_ltrP`, `bigmaxr_gerP`, `bigmaxr_gtrP`
- in `sequences.v`:
  + lemma `closed_seq`
- in `normedtype.v`:
  + lemma `is_intervalPle`
- in `topology.v`:
  + lemma `continuous_cst`
- in `csum.v`:
  + lemma `ub_ereal_sup_adherent_img`

### Infrastructure

### Misc
