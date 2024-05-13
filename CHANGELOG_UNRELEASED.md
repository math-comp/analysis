# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemmas `setC_I`, `bigcup_subset`

- in `set_interval.v`:
  + lemma `interval_set1`

- in `normedtype.v`:
  + lemma `nbhs_right_ltDr`

- in `numfun.v`:
  + lemma `epatch_indic`
  + lemma `restrict_normr`
  + lemmas `funepos_le`, `funeneg_le`

- in `ereal.v`:
  + lemmas `restrict_EFin`

- in `measure.v`:
  + definition `lim_sup_set`
  + lemmas `lim_sup_set_ub`, `lim_sup_set_cvg`, `lim_sup_set_cvg0`

- in `lebesgue_integral.v`:
  + lemma `integral_Sset1`
  + lemma `integralEpatch`
  + lemma `integrable_restrict`
  + lemma `le_integral`
  + lemma `null_set_integral`
  + lemma `EFin_normr_Rintegral`

- in `charge.v`:
  + definition `charge_variation`
  + lemmas `abse_charge_variation`, `charge_variation_continuous`
  + definition `induced`
  + lemmas `semi_sigma_additive_nng_induced`, `dominates_induced`, `integral_normr_continuous`

- in `ftc.v`:
  + definition `indefinite_integral`
  + lemmas `indefinite_integral_near_left`,
    `indefinite_integral_cvg_left`, `indefinite_integral_cvg_at_left`
  + corollary `continuous_FTC2`

### Changed

- in `lebesgue_integral.v`:
  + lemma `measurable_int`: argument `mu` now explicit 

- moved from `lebesgue_integral.v` to `ereal.v`:
  + lemma `funID`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pdivr_mull` -> `lte_pdivrMl`
  + `lte_pdivr_mulr` -> `lte_pdivrMr`
  + `lte_pdivl_mull` -> `lte_pdivlMl`
  + `lte_pdivl_mulr` -> `lte_pdivlMr`
  + `lte_ndivl_mulr` -> `lte_ndivlMr`
  + `lte_ndivl_mull` -> `lte_ndivlMl`
  + `lte_ndivr_mull` -> `lte_ndivrMl`
  + `lte_ndivr_mulr` -> `lte_ndivrMr`
  + `lee_pdivr_mull` -> `lee_pdivrMl`
  + `lee_pdivr_mulr` -> `lee_pdivrMr`
  + `lee_pdivl_mull` -> `lee_pdivlMl`
  + `lee_pdivl_mulr` -> `lee_pdivlMr`
  + `lee_ndivl_mulr` -> `lee_ndivlMr`
  + `lee_ndivl_mull` -> `lee_ndivlMl`
  + `lee_ndivr_mull` -> `lee_ndivrMl`
  + `lee_ndivr_mulr` -> `lee_ndivrMr`
  + `eqe_pdivr_mull` -> `eqe_pdivrMl`
- in `measure.v`:
  + `measurable_restrict` -> `measurable_restrictT`

### Generalized

- in `measure.v`:
  + lemma `measurable_restrict`

### Deprecated

- in `lebesgue_integral.v`:
  + lemmas `integralEindic`, `integral_setI_indic`

### Removed

### Infrastructure

### Misc
