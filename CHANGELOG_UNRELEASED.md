# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemma `ltgte_fin_num`

- in `probability.v`:
  + lemmas `cdf_fin_num`, `lebesgue_stieltjes_cdf_id`

- in `num_normedtype.v`:
  + lemma `nbhs_infty_gtr`
- in `function_spaces.v`:
  + lemmas `cvg_big`, `continuous_big`

- in `realfun.v`:
  + lemma `cvg_addrl_Ny`

- in `constructive_ereal.v`:
  + lemmas `mule_natr`, `dmule_natr`
  + lemmas `inve_eqy`, `inve_eqNy`

- in `uniform_structure.v`:
  + lemma `continuous_injective_withinNx`

- in `constructive_ereal.v`:
  + variants `Ione`, `Idummy_placeholder`
  + inductives `Inatmul`, `IEFin`
  + definition `parse`, `print`
  + number notations in scopes `ereal_dual_scope` and `ereal_scope`
  + notation `- 1` in scopes `ereal_dual_scope` and `ereal_scope`

- in `tvs.v`
  + lemmas `cvg_sum`, `sum_continuous`

- in `normed_module.v`:
  + structure `NormedVector`
  + definitions `normedVectType`, `oo_norm`, `oo_space`
  + lemmas `oo_norm_ge0`, `le_coord_oo_norm`, `ler_oo_normD`, `oo_norm0_eq0`,
    `oo_normZ`, `oo_normMn`, `oo_normN`, `oo_closed_ball_compact`,
    `equivalence_norms`, `linear_findim_continuous`

### Changed

- in `lebesgue_stieltjes_measure.v` specialized from `numFieldType` to `realFieldType`:
  + lemma `nondecreasing_right_continuousP` 
  + definition `CumulativeBounded`

- in `lebesgue_stieltjes_measure.v`, according to generalization of `Cumulative`, modified:
  + lemmas `wlength_ge0`, `cumulative_content_sub_fsum`, `wlength_sigma_subadditive`, `lebesgue_stieltjes_measure_unique`
  + definitions `lebesgue_stieltjes_measure`, `completed_lebesgue_stieltjes_measure`

### Renamed

### Generalized

- in `lebesgue_stieltjes_measure.v` generalized (codomain is now an `orderNbhsType`):
  + lemma `right_continuousW`
  + record `isCumulative`
  + definition `Cumulative`

### Deprecated

### Removed

### Infrastructure

### Misc
