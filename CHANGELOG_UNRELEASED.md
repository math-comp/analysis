# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`

- in `constructive_ereal.v`,
  + new lemmas `mule_def1r`, `mule_def1l`.
- in `real_interval.v`,
  + new lemmas `itv_cNyNye`, `itv_oNyNye`, `itv_cNyye`, `itv_oNyye`, `itv_ccNyeye`,  
    `itv_coNyeye`, `itv_ocNyeye`, `itv_ooNyeye`, `itv_oNyey_bigcup`, `itv_oNyye_bigcup`.

- in `normed_module.v`,
  + new lemmas `cvgeD0`, `cvge0D`, `cvgeN0`, `cvgeB0`, `cvgeZ0`, `cvge0Z`, 
    `gt0_cvgeyM`, `gt0_cvgeMy`, `lt0_cvgeyM`, `lt0_cvgeMy`, `gt0_cvgeNyM`, 
    `gt0_cvgeMNy`, `lt0_cvgeNyM`, `lt0_cvgeMNy`, `cvgeM0`, `cvge0M`, `cvgeM1`, 
    `cvge1M`, `within_econtinuousD`, `within_econtinuousN`, 
    `within_econtinuousB`, `within_econtinuousM`, `within_continuous_fine`, 
    `within_econtinuous_EFin`, `cvge_lt`, `cvge_gt`.
- in `ereal_normedtype.v`,
  + new lemmas `nbhs_right_lte`, `nbhs_left_gte`, `nbhs_right_lee`, `nbhs_left_gee`.
- in `lebesgue_integral_nonneg.v`,
  + new lemma `integral_itvD`.
- in `lebesgue_integral_under.v`,
  + new lemma `econtinuity_under_integral`.

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

### Renamed

- in `real_interval.v`:
  + `itv_cyy` -> `itv_cyey`
  + `itv_oyy` -> `itv_oyey`
  + `itv_cNyy` -> `itv_cNyey`
  + `itv_oNyy` -> `itv_oNyey`

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
