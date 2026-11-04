# Changelog (unreleased)

## [Unreleased]

### Added

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

- new file `negligible_seq.v`:
  + definition `negligible_seq`
  + lemmas `negligible_seq_cvgP`, `negligible_seq_submod_closed`,
    `le_negligible_seq`, `negligible_seq_eqoP`, `negligible_seqXnM`,
    `negligible_seqV`, `negligible_seq_exprnN`

- new file `negligible_seq_harmonic.v`:
  + definitions `harmonic_coord`, `harmonic_dist`, `extend_infty`,
    `lipschitz_at_infty`, `harmonic_lipschitz`
  + lemmas `harmonic_distxx`, `harmonic_dist_infty`, `lipschitz_at_inftyP`,
    `lipschitz_at_infty_le`, `negligible_seq_lipschitz_at_inftyP`,
    `harmonic_dist_ge_inv`, `harmonic_lipschitzW`,
    `lipschitz_at_inftyS_harmonic`, `negligible_seq_harmonic_lipschitzP`

### Changed

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
