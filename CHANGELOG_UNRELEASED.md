# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

### Renamed

- in `sequences.v`:
  + `limn_einf_shift` -> `limn_einf_addl`
  + `series_le_cvg` -> `series_squeeze_is_cvgn`
- in `pseudometric_normed_Zmodule.v`:
  + `PseudoMetricNormedZmod0` -> `PseudoMetricNormedZmodule`
  + `pseudoMetricNormedZmodType` -> `metricNormedZmodType`
  + `PseudoMetricNormedZmod` -> `MetricNormedZmodule`

- in `normed_module.v`:
  + `PseudoMetricNormedZmod_ConvexTvs_isNormedModule` -> `MetricNormedZmod_ConvexTvs_isNormedModule`

- in `tvs.v`:
  + lemma `nbhsT_subproof` -> `nbhsD_subproof`
  + lemma `nbhsT` -> `nbhsD0`
  + lemma `nbhsB` -> `nbhsD`

- in `pseudometric_normed_Zmodule.v`:
  + `continuous_within_itvP` -> `continuous_within_itvccP`
- in `radon_nikodym.v`:
  + `induced_charge` -> `charge_of_density`
  + `dominates_induced` -> `dominates_charge_of_density`

### Generalized

- in `pseudometric_normed_Zmodule.v`:
  + from `pseudoMetricNormedZmodType` to `PseudoMetricNormedZmod0.type`:
    * lemma `le0_ball0`
    * lemma `cvg_bounded`
    * lemma `bounded_cst`
  + from `realFieldType` to `numFieldType`
    * lemma `bounded_funN`
    * lemma `bounded_funD`

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvgD`, `cvg0D`, `cvgD0`, `cvgN`, `cvgNP`, `cvgB`, `cvg0B`, `cvgB0`, `cvgN0`,
    `cvg_sub0`, `cvg0`, `subr_cvg0`
  + lemmas `within_continuousD`, `within_continuousB`, `within_continuousN`
  + lemmas `le_closed_ball`, `closed_ball0`

- in `tvs.v`:
  + lemmas `fun_cvgZ`, `fun_cvgZr`
  + lemmas `nbhsZ`, `nbhs0Z`

- in `esum.v`:
  + lemmas `esum_bigcupT`, `esum_bigcup`

- in `metric_structure.v`:
  + lemmas `metric_sym`, `mdistxx`, `mdist_gt0`
  + lemmas `metric_triangle`, `metric_hausdorff`
- in `measure_theory/measure_function.v`:
  + lemma `cvg_measure_bigcap`

- in `numfun.v`:
  + lemma `itv_partition_nth_ge`
- in `num_normedtype.v`:
    `continuous_within_itvcyP`,
    `continuous_within_itvNycP`, `continuous_within_itvP`,
    `within_continuous_continuous` generalized from `pseudoMetricNormedZmodType` to `pseudoMetricType`
- in `pseudometric_structure.v`:
  + lemma `cvg_nbhsP` generalized from `metricType` to `pseudoMetricType`
- in `realfun.v`:
  + lemmas `cvg_at_rightP`, `cvg_at_leftP`, `cvgr_dnbhsP`, `cvge_at_rightP`, `cvge_at_leftP`, `cvge_dnbhsP` generalized from `realType` to `archiRealFieldType`

- in `realfun.v`:
  + lemma `lhopital`

- in `separation_axioms.v`:
  + lemma `cvg_lim`
- in `constructive_ereal.v`:
  + lemma `bigmaxe_fin_num`

### Deprecated

- in `pseudometric_normed_Zmodule.v`:
  + lemma `fun_cvgD` (use `cvgD` instead)
  + lemma `fun_cvgN` (use `cvgN` instead)

### Removed

- in `normed_module.v`,
  + lemmas `cvge_ge` and `cvge_le`, redundant with existing `cvge_to_ge` and `cvge_to_le`
- in `tvs.v`:
  + structure `PreUniformLmodule`
  + mixin `PreUniformLmodule_isUniformLmodule`
  + structure `UniformLmodule`
  + factory `UniformNmodule_isUniformLmodule`
  + lemma `prod_add_continuous` (remains accessible via the generic `add_continuous` of `TopologicalNmodule.type`)

- in `pseudometric_normred_Zmodule.v`:
  + lemma `pseudoMetricNormedZModType_hausdorff` (deprecated since 1.10.0)

- in `radon_nikodym.v`:
  + notation `induced` (deprecated since 1.15.0)

- in `filter.v`:
  + notation `\near x, P x`
  + notation `\near x & y, P x y`
  + ltac `near_simpl`

### Infrastructure

### Misc
