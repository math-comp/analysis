# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`

- new file `uniform_metrizable.v`

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in file `nat_topology.v`,
  + new lemma `near_infty_after`.
- in file `num_topology.v`,
  + new lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, and `at_right_shift`.
- in `realfun.v`:
  + lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`, 
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`,
    `derivable_oo_LRcontinuousS`

### Changed

- from `pseudometric_structure.v` to `uniform_structure.v`:
  + definition `entourage_`

- from `separation_axioms.v` to `uniform_metrizable.v`:
  + module `countable_uniform`
  + notation `countable_uniform`
  + definition `sup_pseudometric`
  + module `gauge`
    * definition `gauge`
    * lemma `iter_split_ent`
    * lemma `gauge_ent`
    * lemma `gauge_filter`
    * lemma `gauge_refl`
    * lemma `gauge_inv`
    * lemma `gauge_split`
    * lemma `gauge_countable_uniformity`
    * definition `type`
  + lemma `uniform_pseudometric_sup`

- from `separation_axioms.v` to `topology_structure.v`:
  + definition `perfect_set`
  + lemmas `perfectP`, `perfectTP`, `perfectTP_ex`

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
