# Changelog (unreleased)

## [Unreleased]

### Added
- in `normedtype.v`:
  + lemmas `not_near_inftyP`, `not_near_ninftyP`

- in `topology.v`:
  + lemma `filterN`

- in `normedtype.v`:
  + lemma `ninftyN`

- in `derive.v`:
  + lemma `derive_id`
  + lemmas `exp_derive`, `exp_derive1`
  + lemma `derive_cst`
  + lemma `deriveMr`, `deriveMl`

- in `functions.v`:
  + lemmas `mul_funC`
- in `sequences.v`:
  + lemma `cvg_geometric_eseries_half`

- in `lebesgue_measure.v`:
  + definitions `is_open_itv`, `open_itv_cover`
  + lemmas `outer_measure_open_itv_cover`, `outer_measure_open_le`,
    `outer_measure_open`, `outer_measure_Gdelta`, `negligible_outer_measure`

- in `classical_sets.v`:
  + scope `relation_scope` with delimiter `relation`
  + notation `^-1` in `relation_scope` (use to be a local notation)
  + lemma `set_prod_invK` (was a local lemma in `normedtype.v`)
  + definition `diagonal`, lemma `diagonalP`
- in `mathcomp_extra.v`:
  + lemmas `invf_ple`, `invf_lep`

- in `lebesgue_integral.v`:
  + lemma `integralZr`
  
- in `normedtype.v`:
  + lemma `le_closed_ball` 
- in `sequences.v`:
  + theorem `Baire`
  + definition `bounded_fun_norm`
  + lemma `bounded_landau`
  + definition `pointwise_bounded`
  + definition `uniform_bounded`
  + theorem `Banach_Steinhauss`

- in `topology.v`:
  + Structures `PointedFiltered`, `PointedNbhs`, `PointedUniform`, 
    `PseudoPointedMetric`

### Changed
- in `topology.v`:
  + removed the pointed assumptions from `FilteredType`, `Nbhs`, 
    `TopologicalType`, `UniformType`, and `PseudoMetricType`.
  + if you want the original pointed behavior, use the `p` variants
    of the types, so `ptopologicalType` instead of `topologicalType`.
  + generalized most lemmas to no longer depend on pointedness.
    The main exception is for references to `cvg` and `lim` that depend
    on `get` for their definition.
  + `pointed_principal_filter` becomes `principle_filter_type` and 
    requires only `choiceType` instead of `pointedType`
  + `pointed_discrete_topology` becomes `discrete_topology_type` and 
    requires only `choiceType` instead of `pointedType`
  + renamed lemma `discrete_pointed`to `discrete_space_discrete` 
- in `function_space.v`:
  + generalized most lemmas to no longer depend on pointedness.
- in `normedtype.v`:
  + remove superflous parameters in lemmas `not_near_at_rightP` and `not_near_at_leftP`

- in `lebesgue_measure.v`:
  + remove redundant hypothesis from lemma `pointwise_almost_uniform`

- moved from `numfun.v` to `cardinality.v`:
  + lemma `fset_set_comp`

### Renamed

- in `lebesgue_measure.v`:
  + `measurable_exprn` -> `exprn_measurable`
  + `measurable_mulrl` -> `mulrl_measurable`
  + `measurable_mulrr` -> `mulrr_measurable`
  + `measurable_fun_pow` -> `measurable_funX`
  + `measurable_oppe` -> `oppe_measurable`
  + `measurable_abse` -> `abse_measurable`
  + `measurable_EFin` -> `EFin_measurable`
  + `measurable_oppr` -> `oppr_measurable`
  + `measurable_normr` -> `normr_measurable`
  + `measurable_fine` -> `fine_measurable`
  + `measurable_natmul` -> `natmul_measurable`
- in `topology.v`:
  + in mixin `Nbhs_isUniform_mixin`:
    * `entourage_refl_subproof` -> `entourage_diagonal_subproof`
  + in factory `Nbhs_isUniform`:
    * `entourage_refl` -> `entourage_diagonal`
  + in factory `isUniform`:
    * `entourage_refl` -> `entourage_diagonal`

### Generalized

- in `derive.v`:
  + lemma `derivable_cst`

- in `lebesgue_measure.v`:
  + lemma `measurable_funX` (was `measurable_fun_pow`)

- in `lebesgue_integral.v`
  + lemma `ge0_integral_closed_ball`

### Deprecated

### Removed

- in `lebesgue_measure.v`:
  + notation `measurable_fun_sqr` (was deprecated since 0.6.3)
  + notation `measurable_fun_exprn` (was deprecated since 0.6.3)
  + notation `measurable_funrM` (was deprecated since 0.6.3)
  + notation `emeasurable_fun_minus` (was deprecated since 0.6.3)
  + notation `measurable_fun_abse` (was deprecated since 0.6.3)
  + notation `measurable_fun_EFin` (was deprecated since 0.6.3)
  + notation `measurable_funN` (was deprecated since 0.6.3)
  + notation `measurable_fun_opp` (was deprecated since 0.6.3)
  + notation `measurable_fun_normr` (was deprecated since 0.6.3)
  + notation `measurable_fun_fine` (was deprecated since 0.6.3)
- in `topology.v`:
  + turned into Let's (inside `HB.builders`):
    * lemmas `nbhsE_subproof`, `openE_subproof`
    * lemmas `nbhs_pfilter_subproof`, `nbhsE_subproof`, `openE_subproof`
    * lemmas `open_fromT`, `open_fromI`, `open_from_bigU`
    * lemmas `finI_from_cover`, `finI_from_join`
    * lemmas `nbhs_filter`, `nbhs_singleton`, `nbhs_nbhs`
    * lemmas `ball_le`, `entourage_filter_subproof`, `ball_sym_subproof`,
      `ball_triangle_subproof`, `entourageE_subproof`

### Infrastructure

### Misc
