# Changelog (unreleased)

## [Unreleased]

### Added
- in `normedtype.v`:
  + definitions `contraction` and `is_contraction`
  + lemma `contraction_fixpoint_unique`

- in `constructive_ereal.v`:
  + lemmas `ltNye_eq`, `sube_lt0`, `subre_lt0`, `suber_lt0`, `sube_ge0`
  + lemmas `dsubre_gt0`, `dsuber_gt0`, `dsube_gt0`, `dsube_le0`

- in `topology.v`:
  + lemma `near_inftyS`
  + lemma `continuous_closedP`, `closedU`, `pasting`

- in `sequences.v`:
  + lemmas `contraction_dist`, `contraction_cvg`,
    `contraction_cvg_fixed`, `banach_fixed_point`,
    `contraction_unique`
- in `mathcomp_extra.v`:
  + defintion `onem` and notation ``` `1- ```
  + lemmas `onem0`, `onem1`, `onemK`, `onem_gt0`, `onem_ge0`, `onem_le1`, `onem_lt1`,
    `onemX_ge0`, `onemX_lt1`, `onemD`, `onemMr`, `onemM`
- in `signed.v`:
  + lemmas `onem_PosNum`, `onemX_NngNum`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_fine`
- in `lebesgue_integral.v`:
  + lemma `ge0_integral_mscale`
- in `measure.v`:
  + lemma `measurable_funTS`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_indic`

### Changed

- in `measure.v`:
  + generalize `measurable_uncurry`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pinfty_eq` -> `ltey_eq`
- in `sequences.v`:
  + `nneseries_lim_ge0` -> `nneseries_ge0`
- in `constructive_ereal.v`:
  + `le0R` -> `fine_ge0`
  + `lt0R` -> `fine_gt0`
- in `measure.v`:
  + `ring_fsets` -> `ring_finite_set`
  + `discrete_measurable` -> `discrete_measurable_nat`
- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `measure.v`:
  + `cvg_mu_inc` -> `nondecreasing_cvg_mu`
- in `lebesgue_integral.v`:
  + `muleindic_ge0` -> `nnfun_muleindic_ge0`
  + `mulem_ge0` -> `mulemu_ge0`
  + `nnfun_mulem_ge0` -> `nnsfun_mulemu_ge0`

### Removed

### Infrastructure

### Misc
