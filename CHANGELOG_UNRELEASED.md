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

- in `unstable.v`:
  + lemma `seminorm_normrB`

- in `initial_topology.v`:
  + lemma `initial_nbhs_preimage`

- in `topology_structure.v`:
  + definition `nbhs_basis`
  + definition `open_from`

- in `normed_module.v`:
  + lemma `ball_convex_set` (was a `Let`)

- in `tvs.v`:
  + definition `balanced_set`
  + definition `absolutely_convex_set`
  + lemma `absolutely_convex0`
  + definition `absorbing_set`
  + lemma `absolutely_convex_setX`
  + notation `... `+ ...`
  + lemmas `addsetS`, `add0set`, `addsetI`, `addsetA`
  + lemma `continuous_shift`
  + lemma `nbhs_add1set`
  + definition `init_subconvextvs`
  + factory `NbhsBasisAt0_isConvexTvs`
  + definition `filter_from_basis0`
  + factory `NbhsSubbasisAt0_isConvexTvs`
  + definition `finI_fromsubbasis0`
  + lemma `openD`
  + lemma `openB`
  + lemma `nbhsE0`
  + lemma `openZ`
  + lemma `scalerx_continuous`
  + lemma `scalexr_continuous`
  + definition `nbhsbasis_convextvs`
  + definition `open_nbhsbasis_convextvs`
  + definition `open_absconvex_opennbhsbasis`
  + definition `basis_opennbhsbasis`
  + lemma `basis_neqset0`
  + lemma `absorbing_opennbhsbasis`
  + definition `gauge_fun`
  + definition `seminorm_on`
  + definition `seminorm_subbasis`
  + lemmas `nonempty_subbasis`, `mem0_seminorm_subbasis`, `split_seminorm_subbasis`,
    `expand_seminorm_subbasis`
  + lemmas `convex_seminorm_subbasis`, `balanced_seminorm_subbasis`,
    `absolutely_convex_seminorm_subbasis`, `absorbing_seminorm`, `continuous_at0_seminorm`,
    `continuous_seminorm`
  + definitions `gauge_fun_basis`, `seminorm_of`
  + theorem `seminorm_convextvs`
  + lemma `continuous_seminorm_of`
  + lemma `linear_continuous_seminorm`
  + lemma `linear_seminorm_continuous`
  + proposition `lcfun_seminorm`

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

- moved from `trigo.v` to `trigonometry_integral.v`:
  + lemmas `integral0_oneDsqr`, `integral0y_oneDsqr`

- moved from `trigo.v` to `trigonometry_functions.v`:
  + all contents except lemmas `integral0_oneDsqr`, `integral0y_oneDsqr`

- from `normed_module.v` to `tvs.v`:
  + lemma `continuousfor0_continuous` (moved and generalized)

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

- in `tvs.v`:
  + lemma `nbhsT_subproof` -> `nbhsD_subproof`

- in `tvs.v`:
  + lemma `nbhsT` -> `nbhsD0`
  + lemma `nbhsB` -> `nbhsD`

### Generalized

- in `esum.v`:
  + lemmma `le_esum`

- from `pseudometric_normed_Zmodule.v` to `topology_structure.v`:
  + lemma `continuous_comp_cvg`

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
