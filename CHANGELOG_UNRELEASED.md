# Changelog (unreleased)

## [Unreleased]

### Added

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvg0D`, `cvgD0`, `cvg0B`, `cvgB0`, `cvgN0`

- in `normed_module.v`:
  + lemmas `cvg1M`, `cvgM1`, `cvg0M`, `cvgM0`
  + lemmas `cvg1Z`, `cvg0Z`, `cvgZ0`

- in `normal_distribution.v`:
  + definition `post_stddev`
  + lemmas `post_stddev_gt0`, `post_stddevE`
  + definition `post_mean`
  + lemmas `normal_fun_conjugate`, `normal_pdf_conjugate`, `normal_prob_conjugate`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_leq`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`,
    `at_left_shift`, `at_right_shift`
- in `esum.v`:
  + lemmas `pos_esum_ge1`, `le_pos_esum_fine`, `sum_esum_ge`, `le_esum_fine`,
    `subset_esum`, `esum0`, `esum_if_eq_op_set1`, `esum_neq0`, `esum_ge1`
  + lemmas `eq_esummable`, `le_esummable`, `esummableZl`, `esummableZr`,
    `esummableMl`, `esummableMr`, `esummableM`
  + lemmas `esummable_esum_funepos`, `esummable_esum_funeneg`,
     `esummable_esum_fin_num`, `esummable_esumN`
  + lemma `esumE`
  + lemmas `esummable_esumZ`, `esummable_esumD`, `esummableB`

- new files (result of the splitting of `trigo.v`):
  + `elementary_functions/trigo.v`
  + `elementary_functions/trigonometry_functions.v`
  + `elementary_functions/trigonometry_integral.v`

- in `topology_structure.v`:
  + lemma `id_continuous`

- in `derive.v`
  + new lemmas `derive1Dn`, `der1_scaleLR`, `deriveZLR`, `derivableZLR`, 
- in `derive.v`:
  + lemmas `derive1Dn`, `der1_scaleLR`, `deriveZLR`, `derivableZLR`, 
    `derivable_comp_shift`, `derive_comp_shift`, `is_derive_comp_shift`, `derive1_comp_shift`, 
    `near_eq_derive1n_near`, `near_eq_derive1_near`, `near_eq_derive1n`,
    `near_eq_derive1`
  + global instance `is_derive_exp`
  + lemma `derive1_shift`

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

- moved from `trigo.v` to `trigonometry_integral.v`:
  + lemmas `integral0_oneDsqr`, `integral0y_oneDsqr`

- moved from `trigo.v` to `trigonometry_functions.v`:
  + all contents except lemmas `integral0_oneDsqr`, `integral0y_oneDsqr`

- moved from `realfun.v` to `derive.v`: 
  + lemmas `is_deriveV`, `is_derive1_comp`

### Renamed

- in `esum.v`:
  + `summable` -> `esummable`
  + `summable_pinfty` -> `esummable_pinfty`
  + `summableE` -> `esummableE`
  + `summableD` -> `esummableD`
  + `summableN` -> `esummableN`
  + `summableB` -> `esummableB`
  + `summable_funepos` -> `esummable_funepos`
  + `summable_funeneg` -> `esummable_funeneg`
  + `summable_fine_sum` -> `esummable_fine_sum`
  + `summable_cvg` -> `esummable_cvg`
  + `summable_nneseries_lim` -> `esummable_nneseries_lim`
  + `summable_eseries` -> `esummable_eseries`
  + `summable_eseries_esum` -> `esummable_eseries_esum`

- in `lebesgue_integrable.v`:
  + `integrable_summable` -> `integrable_esummable`

- in `lebesgue_integral_nonneg.v`:
  + `summable_integral_dirac` -> `esummable_integral_dirac`
- `mathcomp_extra.v` -> `mathcomp_compat.v`

### Generalized

- in `esum.v`:
  + lemmma `le_esum`

- from `pseudometric_normed_Zmodule.v` to `topology_structure.v`:
  + lemma `continuous_comp_cvg`
- in `derive.v`:
  + lemmas `derive1_comp`, `is_derive1_comp` (`realFieldType` -> `numFieldType`)
  + lemmas `derive_shift`, `is_derive_shift` (function codomain)

### Deprecated

### Removed

- in `unstable.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq` (now in MathComp 2.6.0)

- in `classical_sets.v`:
  + notations `preimage_itv_o_infty`, `preimage_itv_c_infty`,
    `preimage_itv_infty_o`, `preimage_itv_infty_c`
    (deprecated since 1.8.0)

- in `constructive_ereal.v`:
  + notations `maxeMr`, `maxeMl`, `mineMr`, `mineMl`
    (deprecated since 1.8.0)

- in `derive.v`:
  + notation `le0r_derive1_ndecr` (deprecated since 1.9.0)

- in `set_interval.v`:
  + notations `opp_itv_bnd_infty`, `opp_itv_infty_bnd` (deprecated since 1.9.0)

- in `Rstruct.v`:
  + definition `Rinvx` (deprecated since 1.9.0)

- in `real_interval.v`:
  + notations `itv_bnd_infty_bigcup`, `itv_bnd_infty_bigcup0S`, `itv_infty_bnd_bigcup`
    (deprecated since 1.9.0)

- in `num_topology.v`:
  + notations `nbhs_lt`, `nbhs_le` (deprecated since 1.9.0)

- in `normed_module.v`:
  + notation `cvge_sub0` (deprecated since 1.9.0)

- in `num_normedtype.v`:
  + notation `cvgyNP` (deprecated since 1.9.0)

- in `measurable_function.v`:
  + notation `preimage_class_measurable_fun` (deprecated since 1.9.0)

- in `measurable_structure.v`:
  + notations `setDI_closed`, `setDI_semi_setD_closed`, `sedDI_closedP`,
    `setringDI`, `preimage_classes`, `preimage_classes_comp`
    (deprecated since 1.9.0)

### Infrastructure

### Misc
