# Changelog (unreleased)

## [Unreleased]

### Added

- in `sequences.v`:
  + lemma `sdrop_shift`
  + lemma `ge_einfs`
  + lemma `einfs_shift`
  + lemma `limn_einf_shift_new`
  + lemma `limn_einf_shiftS`
  + lemma `limn_einf_cst`
- in `uniform_structure.v`:
  + lemma `unif_continuous_continuous`

- in file `normed_module.v`,
  + new lemmas `bounded_rangeM`, `bounded_rangeMl`, `bounded_rangeMr`, and 
    `bounded_range_max`.
- in file `pseudometric_normed_Zmodule.v`,
  + new lemmas `bounded_range`, `bounded_rangeP`, `bounded_range_exP`, 
    `bounded_range_setU`, `bounded_range_set0`, `bounded_range_set1`, 
    `bounded_rangeW`, `bounded_rangeD`, `bounded_range_comp`, 
    `bounded_range_shift`, `bounded_range_itv_tweak`, and `eq_bounded_range`.

### Changed

- in `esum.v`:
  + level of notation `\esum_ ( i 'in' P ) F`
    from level 41 to 34

- in `lebesgue_integral_definition.v`
  + level of notation `\int[ mu ]_( i 'in' D) F`
    from level 36 to 34 and level of `F` from 36 to 41.
    In particular, this means that `\int[mu]_(x in D) f x * g x`
    now parses as `\int[mu]_(x in D) (f x * g x)`.
- in `sequences.v`,
  + lemmas `is_cvg_series_shiftn`, `near_series_squeeze_is_cvgn`

### Changed

### Renamed

- in `sequences.v`:
  + `limn_einf_shift` -> `limn_einf_addl`
  + `series_le_cvg` -> `series_squeeze_is_cvgn`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
