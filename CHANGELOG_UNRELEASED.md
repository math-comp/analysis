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
    `measure_fam_uubP`, `eq_sfkernel`, `kzero_uub`, `sfinite_finite`,
    `sfinite`, `sfinite_kernel_measure`, `finite_kernel_measure`,
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

### Changed

- in `lebesgue_integral.v`:
  + lemma `xsection_ndseq_closed` generalized from a measure to a family of measures

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

### Generalized

### Deprecated

### Removed

- in `normedtype.v`:
  + instance `Proper_dnbhs_realType`
- in `measure.v`:
  + instances `ae_filter_algebraOfSetsType`, `ae_filter_measurableType`,
  `ae_properfilter_measurableType`
- in `lebesgue_integral.v`
  + lemma `emeasurable_funN` (already in `lebesgue_measure.v`)

### Infrastructure

### Misc
