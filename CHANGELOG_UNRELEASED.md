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

- in `sequences.v`:
  + `lim_sup` -> `limn_sup`
  + `lim_inf` -> `limn_inf`
  + `lim_infN` -> `limn_infN`
  + `lim_supE` -> `limn_supE`
  + `lim_infE` -> `limn_infE`
  + `lim_inf_le_lim_sup` -> `limn_inf_sup`
  + `cvg_lim_inf_sup` -> `cvg_limn_inf_sup`
  + `cvg_lim_supE` -> `cvg_limn_supE`
  + `le_lim_supD` -> `le_limn_supD`
  + `le_lim_infD` -> `le_limn_infD`
  + `lim_supD` -> `limn_supD`
  + `lim_infD` -> `limn_infD`
  + `LimSup.lim_esup` -> `limn_esup`
  + `LimSup.lim_einf` -> `limn_einf`
  + `lim_einf_shift` -> `limn_einf_shift`
  + `lim_esup_le_cvg` -> `limn_esup_le_cvg`
  + `lim_einfN` -> `limn_einfN`
  + `lim_esupN` -> `limn_esupN`
  + `lim_einf_sup` -> `limn_einf_sup`
  + `cvgNy_lim_einf_sup` -> `cvgNy_limn_einf_sup`
  + `cvg_lim_einf_sup` -> `cvg_limn_einf_sup`
  + `is_cvg_lim_einfE` -> `is_cvg_limn_einfE`
  + `is_cvg_lim_esupE` -> `is_cvg_limn_esupE`

- in `lebesgue_measure.v`:
  + `measurable_fun_lim_sup` -> `measurable_fun_limn_sup`
  + `measurable_fun_lim_esup` -> `measurable_fun_limn_esup`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

### Deprecated

### Removed

- `lebesgue_measure_unique` (generalized to `lebesgue_stieltjes_measure_unique`)

- in `sequences.v`:
  + notations `elim_sup`, `elim_inf`
  + `LimSup.lim_esup`, `LimSup.lim_einf`
  + `elim_inf_shift`
  + `elim_sup_le_cvg`
  + `elim_infN`
  + `elim_supN`
  + `elim_inf_sup`
  + `cvg_ninfty_elim_inf_sup`
  + `cvg_ninfty_einfs`
  + `cvg_ninfty_esups`
  + `cvg_pinfty_einfs`
  + `cvg_pinfty_esups`
  + `cvg_elim_inf_sup`
  + `is_cvg_elim_infE`
  + `is_cvg_elim_supE`

- in `lebesgue_measure.v`:
  + `measurable_fun_elim_sup`

### Infrastructure

### Misc
