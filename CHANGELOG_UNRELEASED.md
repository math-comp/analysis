# Changelog (unreleased)

## [Unreleased]

### Added

- in file `normedtype.v`:
  + definition `bigcup_ointsub`
  + lemmas `bigcup_ointsub0`, `open_bigcup_ointsub`, `is_interval_bigcup_ointsub`,
    `bigcup_ointsub_sub`, `open_bigcup_rat`
  + lemmas `mulrl_continuous` and `mulrr_continuous`.
- in file `lebesgue_measure.v`:
  + lemmas `is_interval_measurable`, `open_measurable`, `continuous_measurable_fun`
- in `classical_sets.v`:
  + lemma `preimage_setT`
- in `ereal.v`:
  + definition `expe` with notation `^+`
  + definition `enatmul` with notation `*+` (scope `%E`)
  + definition `ednatmul` with notation `*+` (scope `%dE`)
  + lemmas `fineM`, `enatmul_pinfty`, `enatmul_ninfty`, `EFin_natmul`, `mule2n`, `expe2`,
    `mule_natl`
  + lemmas `ednatmul_pinfty`, `ednatmul_ninfty`, `EFin_dnatmul`, `dmule2n`, `ednatmulE`,
    `dmule_natl`
  + lemmas `sum_fin_num`, `sum_fin_numP`
- in `esum.v`:
  + lemma `esum_set1`
- in `ereal.v`:
  + lemmas `oppeB`, `doppeB`, `fineB`, `dfineB`
- in file `mathcomp_extra.v`:
  + lemma `card_fset_sum1`
- in file `classical_sets.v`:
  + lemmas `setI_II` and `setU_II`
- in file `cardinality.v`:
  + lemma `fset_set_image`, `card_fset_set`, `geq_card_fset_set`,
    `leq_card_fset_set`, `infinite_set_fset`, `infinite_set_fsetP` and
    `fcard_eq`.

### Changed

- in `esumv`:
  + remove one hypothesis in lemmas `reindex_esum`, `esum_image`
- moved from `lebesgue_integral.v` to `lebesgue_measure.v` and generalized
  + hint `measurable_set1`/`emeasurable_set1`

### Renamed

- in `ereal.v`:
  + `num_abs_le` -> `num_abse_le`
  + `num_abs_lt` -> `num_abse_lt`
  + `addooe` -> `addye`
  + `addeoo` -> `addey`
  + `mule_ninfty_pinfty` -> `mulNyy`
  + `mule_pinfty_ninfty` -> `mulyNy`
  + `mule_pinfty_pinfty` -> `mulyy`
  + `mule_ninfty_ninfty` -> `mulNyNy`
  + `lte_0_pinfty` -> `lt0y`
  + `lte_ninfty_0` -> `ltNy0`
  + `lee_0_pinfty` -> `le0y`
  + `lee_ninfty_0` -> `leNy0`
  + `lte_pinfty` -> `ltey`
  + `lte_ninfty` -> `ltNye`
  + `lee_pinfty` -> `leey`
  + `lee_ninfty` -> `leNye`
  + `mulrpinfty_real` -> `real_mulry`
  + `mulpinftyr_real` -> `real_mulyr`
  + `mulrninfty_real` -> `real_mulrNy`
  + `mulninftyr_real` -> `real_mulNyr`
  + `mulrpinfty` -> `mulry`
  + `mulpinftyr` -> `mulyr`
  + `mulrninfty` -> `mulrNy`
  + `mulninftyr` -> `mulNyr`
  + `gt0_mulpinfty` -> `gt0_mulye`
  + `lt0_mulpinfty` -> `lt0_mulye`
  + `gt0_mulninfty` -> `gt0_mulNye`
  + `lt0_mulninfty` -> `lt0_mulNye`
  + `maxe_pinftyl` -> `maxye`
  + `maxe_pinftyr` -> `maxey`
  + `maxe_ninftyl` -> `maxNye`
  + `maxe_ninftyr` -> `maxeNy`
  + `mine_ninftyl` -> `minNye`
  + `mine_ninftyr` -> `mineNy`
  + `mine_pinftyl` -> `minye`
  + `mine_pinftyr` -> `miney`
  + `mulrinfty_real` -> `real_mulr_infty`
  + `mulrinfty` -> `mulr_infty`
- in `realfun.v`:
  + `exp_continuous` -> `exprn_continuous`
- in `sequences.v`:
  + `ereal_pseriesD` -> `nneseriesD`
  + `ereal_pseries0` -> `nneseries0`
  + `ereal_pseries_pred0` -> `nneseries_pred0`
  + `eq_ereal_pseries` -> `eq_nneseries`
  + `ereal_pseries_sum_nat` -> `nneseries_sum_nat`
  + `ereal_pseries_sum` -> `nneseries_sum`
  + `ereal_pseries_mkcond` -> `nneseries_mkcond`
  + `ereal_nneg_series_lim_ge` -> `nneseries_lim_ge`
  + `is_cvg_ereal_nneg_series_cond` -> `is_cvg_nneseries_cond`
  + `is_cvg_ereal_nneg_series` -> `is_cvg_nneseries`
  + `ereal_nneg_series_lim_ge0` -> `nneseries_lim_ge0`
  + `adde_def_nneg_series` -> `adde_def_nneseries`
- in `esum.v`:
  + `ereal_pseries_esum` -> `nneseries_esum`

### Removed

- in `mathcomp_extra.v`:
  + lemmas `natr_absz`, `ge_pinfty`, `le_ninfty`, `gt_pinfty`,
    `lt_ninfty`

### Infrastructure

### Misc
