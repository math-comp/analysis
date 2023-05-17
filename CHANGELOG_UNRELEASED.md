# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemma `globally0`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`
- in `measure.v`:
  + lemma `measurable_fun_bigcup`
- in `sequences.v`:
  + lemma `eq_eseriesl`
- in `lebesgue_measure.v`:
  + lemma `measurable_expR`

- in file `topology.v`,
  + new definitions `basis`, and `second_countable`.
  + new lemmas `clopen_countable` and `compact_countable_base`.
- in `classical_sets.v`:
  + lemmas `set_eq_le`, `set_neq_lt`
- in `set_interval.v`:
  + lemma `set_lte_bigcup`
- in `lebesgue_integral.v`:
  + lemmas `emeasurable_fun_lt`, `emeasurable_fun_le`, `emeasurable_fun_eq`,
    `emeasurable_fun_neq`
  + lemma `integral_ae_eq`
- in file `kernel.v`,
  + new definitions `kseries`, `measure_fam_uub`, `kzero`, `kdirac`,
    `prob_pointed`, `mset`, `pset`, `pprobability`, `kprobability`, `kadd`,
    `mnormalize`, `knormalize`, `kcomp`, and `mkcomp`.
  + new lemmas `eq_kernel`, `measurable_fun_kseries`, `integral_kseries`,
    `measure_fam_uubP`, `eq_sfkernel`, `kzero_uub`,
    `sfinite_kernel`, `sfinite_kernel_measure`, `finite_kernel_measure`,
    `measurable_prod_subset_xsection_kernel`,
    `measurable_fun_xsection_finite_kernel`,
    `measurable_fun_xsection_integral`,
    `measurable_fun_integral_finite_kernel`,
    `measurable_fun_integral_sfinite_kernel`, `lt0_mset`, `gt1_mset`,
    `kernel_measurable_eq_cst`, `kernel_measurable_neq_cst`, `kernel_measurable_fun_eq_cst`,
    `measurable_fun_kcomp_finite`, `mkcomp_sfinite`,
    `measurable_fun_mkcomp_sfinite`, `measurable_fun_preimage_integral`,
    `measurable_fun_integral_kernel`, and `integral_kcomp`.
  + lemma `measurable_fun_mnormalize`
- in `ereal.v`:
  + lemmas `compreDr`, `compreN`
- in `constructive_ereal.v`:
  + lemmas `lee_sqr`, `lte_sqr`, `lee_sqrE`, `lte_sqrE`, `sqre_ge0`,
    `EFin_expe`, `sqreD`, `sqredD`
- in `probability.v`
  + definition of `covariance`
  + lemmas `expectation_sum`, `covarianceE`, `covarianceC`,
    `covariance_fin_num`, `covariance_cst_l`, `covariance_cst_r`,
    `covarianceZl`, `covarianceZr`, `covarianceNl`, `covarianceNr`,
    `covarianceNN`, `covarianceDl`, `covarianceDr`, `covarianceBl`,
    `covarianceBr`, `variance_fin_num`, `varianceZ`, `varianceN`,
    `varianceD`, `varianceB`, `varianceD_cst_l`, `varianceD_cst_r`,
    `varianceB_cst_l`, `varianceB_cst_r`
- in `functions.v`:
  + lemma `sumrfctE`
- in `lebesgue_integral.v`:
  + lemma `integrable_sum`
- in `probability.v`
  + lemma `cantelli`

- in `measure.v`:
  + lemmas `measurable_pair1`, `measurable_pair2`

### Changed

- in `lebesgue_measure.v`
  + `measurable_funrM`, `measurable_funN`, `measurable_fun_exprn`
- in `lebesgue_integral.v`:
  + lemma `xsection_ndseq_closed` generalized from a measure to a family of measures
- in `probability.v`
  + `variance` is now defined based on `covariance` 

### Renamed

- in `derive.v`:
  + `Rmult_rev` -> `mulr_rev`
  + `rev_Rmult` -> `rev_mulr`
  + `Rmult_is_linear` -> `mulr_is_linear`
  + `Rmult_linear` -> `mulr_linear`
  + `Rmult_rev_is_linear` -> `mulr_rev_is_linear`
  + `Rmult_rev_linear` -> `mulr_rev_linear`
  + `Rmult_bilinear` -> `mulr_bilinear`
  + `is_diff_Rmult` -> `is_diff_mulr`
- in `lebesgue_measure.v`
  + `measurable_funN` -> `measurable_oppr`
  + `emeasurable_fun_minus` -> `measurable_oppe`
  + `measurable_fun_abse` -> `measurable_abse`
  + `measurable_EFin` -> `measurable_image_EFin`
  + `measurable_fun_EFin` -> `measurable_EFin`
  + `measurable_fine` -> `measurable_image_fine`
  + `measurable_fun_fine` -> `measurable_fine`
  + `measurable_fun_normr` -> `measurable_normr`
  + `measurable_fun_exprn` -> `measurable_exprn`
  + `emeasurable_fun_max` -> `measurable_maxe`
  + `emeasurable_fun_min` -> `measurable_mine`
  + `measurable_fun_max` -> `measurable_maxr`
  + `measurable_fun_er_map` -> `measurable_er_map`
  + `emeasurable_fun_funepos` -> `measurable_funepos`
  + `emeasurable_fun_funeneg` -> `measurable_funeneg`
  + `measurable_funrM` -> `measurable_mulrl`
- in `measure.v`:
  + `measurable_fun_id` -> `measurable_id`
  + `measurable_fun_cst` -> `measurable_cst`
  + `measurable_fun_comp` -> `measurable_comp`
  + `measurable_funT_comp` -> `measurableT_comp`
  + `measurable_fun_fst` -> `measurable_fst`
  + `measurable_fun_snd` -> `measurable_snd`
  + `measurable_fun_swap` -> `measurable_swap`
  + `measurable_fun_pair` -> `measurable_fun_prod`
- in `lebesgue_integral.v`:
  + `measurable_fun_indic` -> `measurable_indic`

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemma `measurable_fun_sqr` (use `measurable_exprn` instead)
  + lemma `measurable_fun_opp` (use `measurable_oppr` instead)

### Removed

- in `normedtype.v`:
  + instance `Proper_dnbhs_realType`
- in `measure.v`:
  + instances `ae_filter_algebraOfSetsType`, `ae_filter_measurableType`,
  `ae_properfilter_measurableType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_funN` (use `measurableT_comp`) instead
  + lemma `measurable_fun_prod1` (use `measurableT_comp` instead)
  + lemma `measurable_fun_prod2` (use `measurableT_comp` instead)
- in `lebesgue_integral.v`
  + lemma `emeasurable_funN` (was already in `lebesgue_measure.v`, use `measurableT_comp` instead)

### Infrastructure

### Misc
