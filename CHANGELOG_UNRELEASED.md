# Changelog (unreleased)

## [Unreleased]

### Added

- in `boolp.v`:
  + lemma `not_andP`
- in `classical_sets.v`:
  + lemmas `setIIl`, `setIIr`, `setCS`, `setSD`, `setDS`, `setDSS`, `setCI`,
    `setDUr`, `setDUl`, `setIDA`, `setDD`
  + definition `dep_arrow_choiceType`
  + lemma `bigcup_set0`
- in `normedtype.v`:
  + lemma `closed_ereal_le_ereal`
  + lemma `closed_ereal_ge_ereal`
  + lemmas `set0M`, `setM0`, `image_set0_set0`, `subset_set1`, `preimage_set0`
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`
  + lemmas `gee0P`, `sume_ge0`, `lee_sum_nneg`, `lee_sum_nneg_ord`, `lee_sum_nneg_subset`, `lee_sum_nneg_subfset`
  + lemma `lee_addr`
  + lemma `lee_adde`
- in `normedtype.v`:
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`, `geometric_invn`
  + lemmas `increasing_series`, `cvg_shiftS`, `mulrn_arithmetic`,
    `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`,
    `is_cvg_geometric_series`.
- in `classical_sets.v`:
  + new lemmas: `lb_set1`, `ub_lb_set1`, `ub_lb_refl`, `lb_ub_lb`
  + new definitions and lemmas: `infimums`, `infimum`, `infimums_set1`, `is_subset1_infimum`
  + new lemmas: `ge_supremum_Nmem`, `le_infimum_Nmem`, `nat_supremums_neq0`
  + lemmas `ereal_nbhs_pinfty_ge`, `ereal_nbhs_ninfty_le`
  + lemma `oppe_continuous`
  + lemmas `setUCl`, `setDv`
  + lemmas `image_preimage_subset`, `image_subset`, `preimage_subset`

### Changed

- in `classical_sets.v`:
  + the index in `bigcup_set1` generalized from `nat` to some `Type`
  + lemma `bigcapCU` generalized
  + lemmas `preimage_setU` and `preimage_setI` are about the `setU` and `setI` (instead of `bigcup` and `bigcap`)
- lemma `asboolb` moved from `discrete.v` to `boolp.v`
- lemma `exists2NP` moved from `discrete.v` to `boolp.v`
- lemma `neg_or` moved from `discrete.v` to `boolp.v` and renamed to `not_orP`
- definitions `dep_arrow_choiceClass` and `dep_arrow_pointedType`
  slightly generalized and moved from `topology.v` to
  `classical_sets.v`
- the types of the topological notions for `numFieldType` have been moved from `normedtype.v` to `topology.v`
- the topology of extended real numbers has been moved from `normedtype.v` to `ereal.v` (including the notions of filters)
- `numdFieldType_lalgType` in `normedtype.v` renamed to `numFieldType_lalgType` in `topology.v`
- in `ereal.v`:
  + the first argument of `real_of_er` is now maximal implicit
  + the first argument of `is_real` is now maximal implicit
  + generalization of `lee_sum`

### Renamed

- in `classical_sets.v`:
  + `setIDl` -> `setIUl`
  + `setUDl` -> `setUIl`
  + `setUDr` -> `setUIr`
  + `setIDr` -> `setIUl`
  + `setCE` -> `setTD`
  + `preimage_setU` -> `preimage_bigcup`, `preimage_setI` -> `preimage_bigcap`
- in `boolp.v`:
  + `contrap` -> `contra_not`
  + `contrapL` -> `contraPnot`
  + `contrapR` -> `contra_notP`
  + `contrapLR` -> `contraPP`

### Removed

- in `boolp.v`:
  + `contrapNN`, `contrapTN`, `contrapNT`, `contrapTT`
  + `eqNN`
- in `normedtype.v`:
  + `forallN`
  + `eqNNP`
  + `existsN`
- in `discrete.v`:
  + `existsP`
  + `existsNP`

### Infrastructure

### Misc
