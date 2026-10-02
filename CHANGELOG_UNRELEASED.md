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
- in `uniform_structure.v`:
  + lemma `unif_continuous_comp`

- in `initial_topology.v`:
  + lemma `initial_unif_continuous`
  + lemma `initial_unif_continuous_comp`
  + lemma `initial_unif_continuous_comp_fst`
  + lemma `initial_unif_continuous_comp_snd`
  + lemma `initial_nbhs_preimage`

- in `product_topology.v`:
  + lemma `entourage_prod_exS`
  + definition `interchange_prod`
  + lemma `entourage_interchange_prod`
  + lemma `pair_unif_continuous`
  + lemma `fst_unif_continuous`
  + lemma `snd_unif_continuous`

- in `metric_space.v`:
  + definition `prod_mdist`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `PseudoMetricNormedZmodule_add_unif_continuous`
  + lemma `PseudoMetricNormedZmodule_opp_unif_continuous`
  + lemma `standard_scale_continuous`
  + notation `topologicalNmodType`

- in `unstable.v`:
  + definitions `clamp`, `clamp_gele`
  + lemmas `clamp_gemin`, `clamp_lemax`, `minmax_clamp`,
    `clamp_id`, `clamp_min`, `clamp_max`
  + lemma `seminorm_normrB`


- in `topology_structure.v`:
  + lemma `id_continuous`
  + definition `nbhs_basis`
  + definition `openU_from`

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

- in `hahn_banach_theorem.v`
  + theorem `hahn_banach_extension_subctvs`
  + theorem `hahn_banach_extension_initialsubctvs`

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

- moved from `tvs.v` to `pseudometric_normed_Zmodule.v`
  + mixin `PreTopologicalNmodule_isTopologicalNmodule`
  + structure `TopologicalNmodule`
  + lemmas `fun_cvgD`, `cvg_sum`, `sum_continuous`
  + mixin `TopologicalNmodule_isTopologicalZmodule`
  + structure `TopologicalZmodule`, type `topologicalZmodType`
  + lemmas `sub_continuous`, `fun_cvgN`
  + factory `PreTopologicalNmodule_isTopologicalZmodule`
  + mixin `PreUniformNmodule_isUniformNmodule`
  + structure `UniformNmodule`
  + mixin `UniformNmodule_isUniformZmodule`
  + structure `UniformZmodule`
  + factory `PreUniformNmodule_isUniformZmodule`
  + lemma `sub_unif_continuous`

- in `tvs.v`:
  + structure `ConvexTvs` now inherits from `UniformZmodule`

- move to `pseudometric_structure.v`:
  + definitions `closed_ball_`, `closed_ball`
  + lemmas `closure_ballE`, `closed_ballxx`, `closed_ball_closed`, `subset_closed_ball`,
    `subset_closure_half`, `le_closed_ball`

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

### Deprecated

- in `pseudometric_normed_Zmodule.v`:
  + lemma `fun_cvgD` (use `cvgD` instead)
  + lemma `fun_cvgN` (use `cvgN` instead)

### Removed

- in `tvs.v`:
  + structure `PreUniformLmodule`
  + mixin `PreUniformLmodule_isUniformLmodule`
  + structure `UniformLmodule`
  + factory `UniformNmodule_isUniformLmodule`
  + lemma `prod_add_continuous` (remains accessible via the generic `add_continuous` of `TopologicalNmodule.type`)

- in `pseudometric_normred_Zmodule.v`:
  + lemma `pseudoMetricNormedZModType_hausdorff` (deprecated since 1.10.0)

### Infrastructure

### Misc
