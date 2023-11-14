# Changelog (unreleased)

## [Unreleased]

### Added

### Changed
  
### Renamed

- in `charge.v`
  + `isCharge` -> `isSemiSigmaAdditive`

- in `ereal.v`:
  + `le_er_map` -> `le_er_map_in`

- in `sequences.v`:
  + `lim_sup` -> `limn_sup`
  + `lim_inf` -> `limn_inf`
  + `lim_infN` -> `limn_infN`
  + `lim_supE` -> `limn_supE`
  + `lim_infE` -> `limn_infE`
  + `lim_inf_le_lim_sup` -> `limn_inf_sup`
  + `cvg_lim_inf_sup` -> `cvg_limn_inf_sup`
  + `cvg_lim_supE` -> `cvg_limn_supE`
  + `le_lim_supD` -> `le_limn_supD`
  + `le_lim_infD` -> `le_limn_infD`
  + `lim_supD` -> `limn_supD`
  + `lim_infD` -> `limn_infD`
  + `LimSup.lim_esup` -> `limn_esup`
  + `LimSup.lim_einf` -> `limn_einf`
  + `lim_einf_shift` -> `limn_einf_shift`
  + `lim_esup_le_cvg` -> `limn_esup_le_cvg`
  + `lim_einfN` -> `limn_einfN`
  + `lim_esupN` -> `limn_esupN`
  + `lim_einf_sup` -> `limn_einf_sup`
  + `cvgNy_lim_einf_sup` -> `cvgNy_limn_einf_sup`
  + `cvg_lim_einf_sup` -> `cvg_limn_einf_sup`
  + `is_cvg_lim_einfE` -> `is_cvg_limn_einfE`
  + `is_cvg_lim_esupE` -> `is_cvg_limn_esupE`

- in `lebesgue_measure.v`:
  + `measurable_fun_lim_sup` -> `measurable_fun_limn_sup`
  + `measurable_fun_lim_esup` -> `measurable_fun_limn_esup`

- in `sequences.v`:
  + `ereal_nondecreasing_cvg` -> `ereal_nondecreasing_cvgn`
  + `ereal_nondecreasing_is_cvg` -> `ereal_nondecreasing_is_cvgn`
  + `ereal_nonincreasing_cvg` -> `ereal_nonincreasing_cvgn`
  + `ereal_nonincreasing_is_cvg` -> `ereal_nonincreasing_is_cvgn`
  + `ereal_nondecreasing_opp` -> `ereal_nondecreasing_oppn`
  + `nonincreasing_cvg_ge` -> `nonincreasing_cvgn_ge`
  + `nondecreasing_cvg_le` -> `nondecreasing_cvgn_le`
  + `nonincreasing_cvg` -> `nonincreasing_cvgn`
  + `nondecreasing_cvg` -> `nondecreasing_cvgn`
  + `nonincreasing_is_cvg` -> `nonincreasing_is_cvgn`
  + `nondecreasing_is_cvg` -> `nondecreasing_is_cvgn`
  + `near_nonincreasing_is_cvg` -> `near_nonincreasing_is_cvgn`
  + `near_nondecreasing_is_cvg` -> `near_nondecreasing_is_cvgn`
  + `nondecreasing_dvg_lt` -> `nondecreasing_dvgn_lt`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

- in `lebesgue_integral.v`:
  + weaken an hypothesis of `integral_ae_eq`
- in `classical_sets.v`:
  + `set_nil` generalized to `eqType`

### Deprecated

### Removed

- `lebesgue_measure_unique` (generalized to `lebesgue_stieltjes_measure_unique`)

- in `sequences.v`:
  + notations `elim_sup`, `elim_inf`
  + `LimSup.lim_esup`, `LimSup.lim_einf`
  + `elim_inf_shift`
  + `elim_sup_le_cvg`
  + `elim_infN`
  + `elim_supN`
  + `elim_inf_sup`
  + `cvg_ninfty_elim_inf_sup`
  + `cvg_ninfty_einfs`
  + `cvg_ninfty_esups`
  + `cvg_pinfty_einfs`
  + `cvg_pinfty_esups`
  + `cvg_elim_inf_sup`
  + `is_cvg_elim_infE`
  + `is_cvg_elim_supE`

- in `lebesgue_measure.v`:
  + `measurable_fun_elim_sup`

### Infrastructure

### Misc
