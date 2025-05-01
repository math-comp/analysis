# Changelog (unreleased)

## [Unreleased]

### Added

- in `probability.v`:
  + lemmas `eq_bernoulli`, `eq_bernoulliV2`

- in `measure.v`:
  + lemmas `mnormalize_id`, `measurable_fun_eqP`

- in `ftc.v`:
  + lemma `integrable_locally`

- in `constructive_ereal.v`:
  + lemma `EFin_bigmax`

- in `mathcomp_extra.v`:
  + lemmas `inr_inj`, `inl_inj`

- in `classical_sets.v`:
  + lemmas `in_set1`, `inr_in_set_inr`, `inl_in_set_inr`, `mem_image`, `mem_range`, `image_f`
  + lemmas `inr_in_set_inl`, `inl_in_set_inl`

- in `lebesgue_integral_approximation.v` (now `measurable_fun_approximation.v`):
  + lemma `measurable_prod`
  + lemma `measurable_fun_lte`
  + lemma `measurable_fun_lee`
  + lemma `measurable_fun_eqe`
  + lemma `measurable_poweR`

- in `exp.v`:
  + lemma `poweRE`

- in `exp.v`:
  + lemmas `lnNy`, `powR_cvg0`, `derivable_powR`, `powR_derive1`
  + Instance `is_derive1_powR`
- in `realfun.v`:
  + lemma `cvge_ninftyP`

- in `boolp.v`:
  + lemmas `orW`, `or3W`, `or4W`
  
- in `classical_sets.v`:
  + lemmas `set_cst`, `image_nonempty`

- in `unstable.v`:
  + lemmas `eq_exists2l`, `eq_exists2r`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`
- in `functions.v`:
  + lemma `natmulfctE`

- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`

- in `ereal.v`:
  + lemmas `ereal_sup_cst`, `ereal_inf_cst`,
    `ereal_sup_pZl`, `ereal_supZl`, `ereal_inf_pZl`, `ereal_infZl`

- in `sequences.v`:
  + lemmas `ereal_inf_seq`, `ereal_sup_seq`

### Changed

- in `pi_irrational`:
  + definition `rational`

### Renamed

- in `kernel.v`:
  + `isFiniteTransition` -> `isFiniteTransitionKernel`

- in `lebesgue_integral_approximation.v`:
  + `emeasurable_fun_lt` -> `measurable_lte`
  + `emeasurable_fun_le` -> `measurable_lee`
  + `emeasurable_fun_eq` -> `measurable_lee`
  + `emeasurable_fun_neq` -> `measurable_neqe`

- file `lebesgue_integral_approximation.v` -> `measurable_fun_approximation.v`

- in `ereal.v`:
  + `ereal_sup_le` -> `ereal_sup_ge`

### Generalized

- in `normedtype.v`:
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`
- in `functions.v`:
  + `fct_sumE`, `addrfctE`, `sumrfctE` (from `zmodType` to `nmodType`)
  + `scalerfctE` (from `pointedType` to `Type`)

- in `measurable_realfun.v`
  + lemma `measurable_ln`

### Deprecated

### Removed

- in `functions.v`:
  + definitions `fct_ringMixin`, `fct_ringMixin` (was only used in an `HB.instance`)

- in `measurable_realfun.v`:
  + notation `measurable_fun_ln` (deprecated since 0.6.3)
  + notations `emeasurable_itv_bnd_pinfty`, `emeasurable_itv_ninfty_bnd` (deprecated since 0.6.2)
  + notation `measurable_fun_lim_sup` (deprecated since 0.6.6)
  + notation `measurable_fun_max` (deprecated since 0.6.3)
  + notation `measurable_fun_er_map` (deprecated since 0.6.3)
  + notations `emeasurable_funN`, `emeasurable_fun_max`, `emeasurable_fun_min`,
    `emeasurable_fun_funepos`, `emeasurable_fun_funeneg` (deprecated since 0.6.3)
  + notation `measurable_fun_lim_esup` (deprecated since 0.6.6)

- in `measure.v`:
  + notation `measurable_fun_ext` (deprecated since 0.6.2)
  + notations `measurable_fun_id`, `measurable_fun_cst`, `measurable_fun_comp` (deprecated since 0.6.3)
  + notation `measurable_funT_comp` (deprecated since 0.6.3)

### Infrastructure

### Misc
