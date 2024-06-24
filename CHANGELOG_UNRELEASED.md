# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemma `ball_subspace_ball`

- in `classical_sets.v`:
  + lemma `setDU`

- in `measure.v`:
  + definition `completed_measure_extension`
  + lemma `completed_measure_extension_sigma_finite`

- in `lebesgue_stieltjes_measure.v`:
  + definition `completed_lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + definition `completed_lebesgue_measure`
  + lemma `completed_lebesgue_measure_is_complete`
  + definition `completed_algebra_gen`
  + lemmas `g_sigma_completed_algebra_genE`, `negligible_sub_caratheodory`,
    `completed_caratheodory_measurable`
- in `ftc.v`:
  + lemma `FTC1` (specialization of the previous `FTC1` lemma, now renamed to `FTC1_lebesgue_pt`)

### Changed

- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

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

- in `ftc.v`:
  + `FTC1` -> `FTC1_lebesgue_pt`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
