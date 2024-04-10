# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_recl`

- in `sequences.v`:
  + lemma `nneseries_recl`

- in `measure.v`:
  + definition `subset_sigma_subadditive`
  + factory `isSubsetOuterMeasure`

- in file `classical_sets.v`
  + notations `\bigcup_(i >= n) F i` and `\bigcap_(i >= n) F i`
  + lemmas `bigcup_addn`, `bigcap_addn`

- in file `sequences.v`
  + lemma `nneseries_addn`

### Changed

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

### Generalized

- in `constructive_ereal.v`:
  + `gee_pMl` (was `gee_pmull`)

- in `sequences.v`:
  + lemmas `eseries0`, `nneseries_split`

### Deprecated

### Removed

### Infrastructure

### Misc
