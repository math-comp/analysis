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

### Changed

- in `hoelder.v`:
  + definition `Lnorm` now `HB.lock`ed
- in `lebesgue_integral.v`:
  + `integral_dirac` now uses the `\d_` notation

- in `measure.v`:
  + order of parameters changed in `semi_sigma_additive_is_additive`,
    `isMeasure`

### Renamed

- in `charge.v`
  + `isCharge` -> `isSemiSigmaAdditive`
- in `reals.v`:
  + lemma `le_inf`
- in `constructive_ereal.v`:
  + lemma `le_er_map`
- new `lebesgue_stieltjes_measure.v`:
  + notation `right_continuous`
  + lemmas `right_continuousW`, `nondecreasing_right_continuousP`
  + mixin `isCumulative`, structure `Cumulative`, notation `cumulative`
  + `idfun` instance of `Cumulative`
  + `hlength`, `hlength0`, `hlength_singleton`, `hlength_setT`, `hlength_itv`,
    `hlength_finite_fin_num`, `finite_hlengthE`, `hlength_itv_bnd`, `hlength_infty_bnd`,
    `hlength_bnd_infty`, `pinfty_hlength`, `hlength_itv_ge0`, `hlength_Rhull`,
    `le_hlength_itv`, `le_hlength`, `hlength_semi_additive`, `hlength_ge0`
  + content instance of `hlength`
  + `hlength_content_sub_fsum`,
    `hlength_sigma_sub_additive`, `hlength_sigma_finite`
  + measure instance of `hlength`
  + definition `lebesgue_stieltjes_measure`

### Changed

- in `lebesgue_measure.v`:
  + are now prefixed with `LebesgueMeasure`:
    * `hlength`, `hlength0`, `hlength_singleton`, `hlength_setT`, `hlength_itv`,
      `hlength_finite_fin_num`, `finite_hlengthE`, `hlength_infty_bnd`,
      `hlength_bnd_infty`, `pinfty_hlength`, `hlength_itv_ge0`, `hlength_Rhull`,
      `le_hlength_itv`, `le_hlength`, `hlength_ge0`, `hlength_semi_additive`,
      `hlength_sigma_sub_additive`, `hlength_sigma_finite`
  + `lebesgue_measure` now defined with `lebesgue_stieltjes_measure`
- moved from `lebesgue_measure.v` to `lebesgue_stieltjes_measure.v`
  + notations `_.-ocitv`, `_.-ocitv.-measurable`
  + definitions `ocitv`, `ocitv_display`
  + lemmas `is_ocitv`, `ocitv0`, `ocitvP`, `ocitvD`, `ocitvI`

### Renamed

- in `ereal.v`:
  + `le_er_map` -> `le_er_map_in`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

### Deprecated

### Removed

### Infrastructure

### Misc
