# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_recl`

- in `sequences.v`:
  + lemma `nneseries_recl`

- in file `mathcomp_extra.v`:
  + module `Order`
    * definitions `disp_t`, `default_display`

- in `measure.v`:
  + definition `subset_sigma_subadditive`
  + factory `isSubsetOuterMeasure`

- in file `classical_sets.v`
  + notations `\bigcup_(i >= n) F i` and `\bigcap_(i >= n) F i`
  + lemmas `bigcup_addn`, `bigcap_addn`

- in file `sequences.v`
  + lemma `nneseries_addn`
- in `lebesgue_integral.v`:
  + lemmas `integrableMl`, `integrableMr`

- in `realfun.v`
  + lemmas `total_variation_nondecreasing`, `total_variation_bounded_variation`
- new file `theories/all_analysis.v`

- in `normedtype.v`:
  + lemma `not_near_at_leftP`

### Changed

- in `forms.v`:
  + notation ``` u ``_ _ ```

- in `trigo.v`:
  + definitions `sin`, `cos`, `acos`, `asin`, `atan` are now HB.locked
- in `sequences.v`:
  + definition `expR` is now HB.locked

### Renamed

- in `constructive_ereal.v`:
  + `gee_pmull` -> `gee_pMl`
  + `gee_addl` -> `geeDl`
  + `gee_addr` -> `geeDr`
  + `gte_addl` -> `gteDl`
  + `gte_addr` -> `gteDr`
  + `lte_subl_addr` -> `lteBlDr`
  + `lte_subl_addl` -> `lteBlDl`
  + `lte_subr_addr` -> `lteBrDr`
  + `lte_subr_addl` -> `lteBrDl`
  + `lee_subl_addr` -> `leeBlDr`
  + `lee_subl_addl` -> `leeBlDl`
  + `lee_subr_addr` -> `leeBrDr`
  + `lee_subr_addl` -> `leeBrDl`

- in `measure.v`:
  + `sub_additive` -> `subadditive`
  + `sigma_sub_additive` -> `measurable_subset_sigma_subadditive`
  + `content_sub_additive` -> `content_subadditive`
  + `ring_sigma_sub_additive` -> `ring_sigma_subadditive`
  + `Content_SubSigmaAdditive_isMeasure` -> `Content_SigmaSubAdditive_isMeasure`
  + `measure_sigma_sub_additive` -> `measure_sigma_subadditive`
  + `measure_sigma_sub_additive_tail` -> `measure_sigma_subadditive_tail`

- in `classical_sets.v`:
  + `notin_set` -> `notin_setE`

- in `signed.v`:
  + `num_le_maxr` -> `num_le_max`
  + `num_le_maxl` -> `num_ge_max`
  + `num_le_minr` -> `num_le_min`
  + `num_le_minl` -> `num_ge_min`
  + `num_lt_maxr` -> `num_lt_max`
  + `num_lt_maxl` -> `num_gt_max`
  + `num_lt_minr` -> `num_lt_min`
  + `num_lt_minl` -> `num_gt_min`

- in `constructive_ereal.v`:
  + `num_lee_maxr` -> `num_lee_max`
  + `num_lee_maxl` -> `num_gee_max`
  + `num_lee_minr` -> `num_lee_min`
  + `num_lee_minl` -> `num_gee_min`
  + `num_lte_maxr` -> `num_lte_max`
  + `num_lte_maxl` -> `num_gte_max`
  + `num_lte_minr` -> `num_lte_min`
  + `num_lte_minl` -> `num_gte_min`

### Generalized

- in `constructive_ereal.v`:
  + `gee_pMl` (was `gee_pmull`)

- in `sequences.v`:
  + lemmas `eseries0`, `nneseries_split`

- in `lebesgue_integral.v`:
  + lemma `ge0_integral_bigcup`
- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2` (from `semiRingOfSetType` to `Type`)
  + lemmas `caratheodory_measurable_mu_ext`, `measurableM`, `measure_dominates_trans`, `ess_sup_ge0`
    definitions `preimage_classes`, `measure_dominates`, `ess_sup`
	(from `measurableType` to `semiRingOfSetsType`)
  + lemmas ` measurable_prod_measurableType`, `measurable_prod_g_measurableTypeR` (from `measurableType` to `algebraOfSetsType`)

### Deprecated

- in `classical_sets.v`:
  + `notin_set` (use `notin_setE` instead)

### Removed

- in `lebesgue_integral.v`:
  + `integrablerM`, `integrableMr` (were deprecated since version 0.6.4)

- in `measure.v`:
  + lemmas `prod_salgebra_set0`, `prod_salgebra_setC`, `prod_salgebra_bigcup`
    (use `measurable0`, `measurableC`, `measurable_bigcup` instead)
- in `derive.v`:
  + definition `mulr_rev`
  + canonical `rev_mulr`
  + lemmas `mulr_is_linear`, `mulr_rev_is_linear`

- in `forms.v`
  + canonical `rev_mulmx`
  + structure `revop`

### Infrastructure

### Misc
