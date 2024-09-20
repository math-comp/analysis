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
- in `ftc.v`:
  + lemmas `integration_by_parts`, `Rintegration_by_parts`

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
- in `measure.v`:
  + lemma `measurable_neg`, `measurable_or`

- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_eqr`, `measurable_fun_indic`, `measurable_fun_dirac`,
    `measurable_fun_addn`, `measurable_fun_maxn`, `measurable_fun_subn`, `measurable_fun_ltn`,
    `measurable_fun_leq`, `measurable_fun_eqn`
  + module `NGenCInfty`
    * definition `G`
    * lemmas `measurable_itv_bounded`, `measurableE`
- in `continuous_FTC1_closed`:
  + corollary `continuous_FTC1_closed`

- in `lebesgue_integral.v`:
  + lemma `locally_integrableS`

- in `normedtype.v`:
  + lemmas `nbhs_right_ltW`, `cvg_patch`

- in `set_interval.v`:
  + lemma `subset_itvSoo`

- in `lebesgue_integral.v`:
  + lemma `integrable_locally_restrict`
  + lemma `near_davg`
  + lemma `lebesgue_pt_restrict`

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

- in `mathcomp_extra.v`:
  + lemma `bij_forall`

- in `normedtype.v`:
  + lemma `cvgyNP`

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

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

- in `lebesgue_measure.v`:
  + remove redundant hypothesis from lemma `pointwise_almost_uniform`

- moved from `numfun.v` to `cardinality.v`:
  + lemma `fset_set_comp`
- in `ftc.v`:
  + lemma `FTC1_lebesgue_pt`, corollaries `FTC1`, `FTC1Ny`: integrability hypothesis weakened

- in `lebesgue_integral.v`:
  + lemma `nice_lebesgue_differentiation`: change the local integrability hypothesis to easy application

- in `normedtype.v`:
  + lemma `continuous_within_itvP`: change the statement to use the notation `[/\ _, _ & _]`

- in `normedtype.v`:
  + remove superflous parameters in lemmas `not_near_at_rightP` and `not_near_at_leftP`

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
