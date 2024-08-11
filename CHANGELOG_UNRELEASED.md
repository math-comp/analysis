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
  + lemmas `not_near_inftyP` `not_near_ninftyP`

- in `topology.v`:
  + lemma `filterN`

- in `normedtype.v`:
  + lemma `ninftyN`

### Changed

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
