# Changelog (unreleased)

## [Unreleased]

### Added
- in `measure.v`:
  + lemma `lebesgue_regularity_outer`

- in `lebesgue_measure.v`:
  + lemma `closed_measurable`

- in file `lebesgue_measure.v`,
  + new lemmas `lebesgue_nearly_bounded`, and `lebesgue_regularity_inner`.
- in file `measure.v`,
  + new lemmas `measureU0`, `nonincreasing_cvg_mu`, and `epsilon_trick0`.
- in file `real_interval.v`,
  + new lemma `bigcup_itvT`.
- in file `topology.v`,
  + new lemma `uniform_nbhsT`.

- in file `topology.v`,
  + new definition `set_nbhs`.
  + new lemmas `filterI_iter_sub`, `filterI_iterE`, `finI_fromI`, 
    `filterI_iter_finI`, `smallest_filter_finI`, and `set_nbhsP`.

- in file `lebesgue_measure.v`,
  + new lemmas `pointwise_almost_uniform`, and 
    `ae_pointwise_almost_uniform`.
- in `measure.v`:
  + lemmas `measurable_pair1`, `measurable_pair2`
  + lemma `covariance_le`
- in `mathcomp_extra.v`
  + definition `coefE` (will be in MC 2.1/1.18)
  + lemmas `deg2_poly_canonical`, `deg2_poly_factor`, `deg2_poly_min`,
    `deg2_poly_minE`, `deg2_poly_ge0`, `Real.deg2_poly_factor`,
    `deg_le2_poly_delta_ge0`, `deg_le2_poly_ge0`
    (will be in MC 2.1/1.18)
  + lemma `deg_le2_ge0`
  + new lemmas `measurable_subring`, and `semiring_sigma_additive`.
  + added factory `Content_SubSigmaAdditive_isMeasure`

- in `lebesgue_integral.v`:
  + lemmas `integrableP`, `measurable_int`
- in `exp.v`:
  + lemmas `power_posrM`, `gt0_ler_power_pos`

- in `mathcomp_extra.v`:
  + definition `min_fun`, notation `\min`
- in `classical_sets.v`:
  + lemmas `set_predC`, `preimage_true`, `preimage_false`
- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_ltr`, `measurable_minr`

### Changed

- moved from `lebesgue_measure.v` to `real_interval.v`:
  + lemmas `set1_bigcap_oc`, `itv_bnd_open_bigcup`, `itv_open_bnd_bigcup`,
    `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`
  
- moved from `functions.v` to `classical_sets.v`: `subsetP`.

### Renamed

- in `boolp.v`:
  + `mextentionality` -> `mextensionality`
  + `extentionality` -> `extensionality`
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
  + `isMeasure0` -> ``Content_isMeasure`
- in `lebesgue_integral.v`:
  + `measurable_fun_indic` -> `measurable_indic`
- in `measure.v`:
  + `Hahn_ext` -> `measure_extension`
  + `Hahn_ext_ge0` -> `measure_extension_ge0`
  + `Hahn_ext_sigma_additive` -> `measure_extension_semi_sigma_additive`
  + `Hahn_ext_unique` -> `measure_extension_unique`
  + `RingOfSets_from_semiRingOfSets` -> `SemiRingOfSets_isRingOfSets`
  + `AlgebraOfSets_from_RingOfSets` -> `RingOfSets_isAlgebraOfSets`
  + `Measurable_from_algebraOfSets` -> `AlgebraOfSets_isMeasurable`
  + `ring_sigma_additive` -> `ring_semi_sigma_additive`
- in `exp.v`:
  + `expK` -> `expRK`

### Generalized

### Deprecated

- in `lebesgue_measure.v`:
  + lemma `measurable_fun_sqr` (use `measurable_exprn` instead)
  + lemma `measurable_fun_opp` (use `measurable_oppr` instead)
- in `exp.v`:
  + lemmas `convex_expR`, `ler_power_pos`

### Removed

### Infrastructure

### Misc
