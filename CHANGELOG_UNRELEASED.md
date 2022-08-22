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
- in `fsbigop.v`:
  + lemmas `lee_fsum_nneg_subset`, `lee_fsum`
- in `classical_sets.v`:
  + lemmas `subset_fst_set`, `subset_snd_set`, `fst_set_fst`, `snd_set_snd`,
    `fset_setM`, `snd_setM`, `fst_setMR`
  + lemmas `xsection_snd_set`, `ysection_fst_set`

### Changed

- in `measure.v`:
  + generalize `measurable_uncurry`
- in `esum.v`:
  + definition `esum`
- moved from `lebesgue_integral.v` to `classical_sets.v`:
  + `mem_set_pair1` -> `mem_xsection`
  + `mem_set_pair2` -> `mem_ysection`
- in `topology.v`:
  + generalize `continuousP`
- in `lebesgue_measure.v`:
  + generalize `continuous_measurable_fun`

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
- in `esum.v`:
  + `esum0` -> `esum1`

- in `topology.v`:
  + `continuousP` -> `continuousTP`
- in `lebesgue_measure.v`:
  + `continuous_measurable_fun` -> `continuousT_measurable_fun`

### Removed

- in `esum.v`:
  + lemma `fsetsP`, `sum_fset_set`

### Infrastructure

### Misc
