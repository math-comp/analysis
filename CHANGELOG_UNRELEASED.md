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

### Changed

- in `forms.v`:
  + notation ``` u ``_ _ ```

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
- in `forms.v`:
  + structure `revop`

### Infrastructure

### Misc
