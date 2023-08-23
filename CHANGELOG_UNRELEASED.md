# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemmas `gt0_fin_numE`, `lt0_fin_numE`

- in `charge.v`:
  + factory `isCharge`
  + Notations `.-negative_set`, `.-positive_set`

- in `measure.v`:
  + lemmas `negligibleI`, `negligible_bigsetU`, `negligible_bigcup`

- in `reals.v`:
  + lemma `le_inf`
- in `constructive_ereal.v`:
  + lemmas `le_er_map`, `er_map_idfun`
- new `lebesgue_stieltjes_measure.v`:
  + notation `right_continuous`
  + lemmas `right_continuousW`, `nondecreasing_right_continuousP`
  + mixin `isCumulative`, structure `Cumulative`, notation `cumulative`
  + `idfun` instance of `Cumulative`
  + `wlength`, `wlength0`, `wlength_singleton`, `wlength_setT`, `wlength_itv`,
    `wlength_finite_fin_num`, `finite_wlength_itv`, `wlength_itv_bnd`, `wlength_infty_bnd`,
    `wlength_bnd_infty`, `infinite_wlength_itv`, `wlength_itv_ge0`, `wlength_Rhull`,
    `le_wlength_itv`, `le_wlength`, `wlength_semi_additive`, `wlength_ge0`,
    `lebesgue_stieltjes_measure_unique`
  + content instance of `hlength`
  + `cumulative_content_sub_fsum`,
    `wlength_sigma_sub_additive`, `wlength_sigma_finite`
  + measure instance of `hlength`
  + definition `lebesgue_stieltjes_measure`
- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`

- in `lebesgue_measure.v`:
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`
- in `convex.v`:
  + lemmas `conv_gt0`, `convRE`

- in `exp.v`:
  + lemmas `concave_ln`, `conjugate_powR`

- in file `lebesgue_integral.v`,
  + new lemmas `integral_le_bound`, `continuous_compact_integrable`, and 
    `lebesgue_differentiation_continuous`.

- in `normedtype.v`:
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`

- in `lebesgue_measure.v`:
  + lemma `measurable_ball`

- in file `normedtype.v`,
  + new lemmas `normal_openP`, `uniform_regular`,
    `regular_openP`, and `pseudometric_normal`.
- in file `topology.v`,
  + new definition `regular_space`.
  + new lemma `ent_closure`.

- in `lebesgue_measure.v`:
  + lemma `measurable_mulrr`

- in `constructive_ereal.v`:
  + lemma `eqe_pdivr_mull`

- new file `hoelder.v`:
  + definition `Lnorm`, notations `'N[mu]_p[f]`, `'N_p[f]`
  + lemmas `Lnorm1`, `Lnorm_ge0`, `eq_Lnorm`, `Lnorm_eq0_eq0`
  + lemma `hoelder`

- in file `lebesgue_integral.v`,
  + new lemmas `simple_bounded`, `measurable_bounded_integrable`, 
    `compact_finite_measure`, `approximation_continuous_integrable`

- in `sequences.v`:
  + lemma `cvge_harmonic`

- in `mathcomp_extra.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq`

- in `constructive_ereal.v`:
  + lemma `bigmaxe_fin_num`
- in `ereal.v`:
  + lemmas `uboundT`, `supremumsT`, `supremumT`, `ereal_supT`, `range_oppe`,
    `ereal_infT`

- in `measure.v`:
  + definition `ess_sup`, lemma `ess_sup_ge0`
- in `convex.v`:
  + definition `convex_function`

- in `exp.v`:
  + lemmas `ln_le0`, `ger_powR`, `ler1_powR`, `le1r_powR`, `ger1_powR`,
    `ge1r_powR`, `ge1r_powRZ`, `le1r_powRZ`

- in `hoelder.v`:
  + lemmas `lnormE`, `hoelder2`, `convex_powR`

- in `lebesgue_integral.v`:
  + lemma `ge0_integral_count`

- in `exp.v`:
  + lemmas `powRDm1`, `poweRN`, `poweR_lty`, `lty_powerRy`, `gt0_ler_poweR`

- in `hoelder.v`:
  + lemmas `Lnorm_powR_K`, `oneminvp`, `minkowski`

### Changed

- in `hoelder.v`:
  + definition `Lnorm` now `HB.lock`ed
- in `lebesgue_integral.v`:
  + `integral_dirac` now uses the `\d_` notation

- in `measure.v`:
  + order of parameters changed in `semi_sigma_additive_is_additive`,
    `isMeasure`

- in `lebesgue_measure.v`:
  + are now prefixed with `LebesgueMeasure`:
    * `hlength`, `hlength0`, `hlength_singleton`, `hlength_setT`, `hlength_itv`,
      `hlength_finite_fin_num`, `hlength_infty_bnd`,
      `hlength_bnd_infty`, `hlength_itv_ge0`, `hlength_Rhull`,
      `le_hlength_itv`, `le_hlength`, `hlength_ge0`, `hlength_semi_additive`,
      `hlength_sigma_sub_additive`, `hlength_sigma_finite`, `lebesgue_measure`
    * `finite_hlengthE` renamed to `finite_hlentgh_itv`
    * `pinfty_hlength` renamed to `infinite_hlength_itv`
  + `lebesgue_measure` now defined with `lebesgue_stieltjes_measure`
  + `lebesgue_measure_itv` does not refer to `hlength` anymore
- moved from `lebesgue_measure.v` to `lebesgue_stieltjes_measure.v`
  + notations `_.-ocitv`, `_.-ocitv.-measurable`
  + definitions `ocitv`, `ocitv_display`
  + lemmas `is_ocitv`, `ocitv0`, `ocitvP`, `ocitvD`, `ocitvI`

### Renamed

- in `charge.v`
  + `isCharge` -> `isSemiSigmaAdditive`

- in `ereal.v`:
  + `le_er_map` -> `le_er_map_in`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

### Deprecated

### Removed

- `lebesgue_measure_unique` (generalized to `lebesgue_stieltjes_measure_unique`)

### Infrastructure

### Misc
