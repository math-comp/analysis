# Changelog (unreleased)

## [Unreleased]

### Added
- in `topology_structure.v`
  + lemma `closed_Ndense`

- in `pseudometric_normed_Zmodule.v`
  + lemma `nbhs0_add`
  + lemma `hausdorff_convextvs`

- in `tvs.v`
  + lemma `closure_convextvs`, `closure_addset`
  + lemma `accessible field`
  + lemma `hausdorff_init_convextvs`
  + definition `closed_nbhsbasis_convextvs`
  + lemma `has_closed_nbhs_basis`
  + lemma `hausdorff_seminorm_on`
  + lemma `seminorm_of_neq0`
  + lemma `continuous_closedkernel`

- in `hahn_banach_theorem.v`
  + definition `linepred` and `line`
  + lemma `line_linepred`
  + subLmodule structure on `line`
  + lemma `scaler_eq0` and `sclaeIl` (TO BE MOVED)
  + lemma hahn_banach_extension_hausdorff

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`

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

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc