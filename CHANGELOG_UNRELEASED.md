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
- in `mathcomp_extra.v`
  + lemmas `ge0_ler_normr`, `gt0_ler_normr`, `le0_ger_normr` and `lt0_ger_normr`
  
- in `probability.v`:
  + definition `mmt_gen_fun`, `chernoff`
  
- in `lebesgue_integral.v`:
  + `mfun` instances for `expR` and `comp`

- in `charge.v`:
  + lemmas `dominates_cscale`, `Radon_Nikodym_cscale`
  + definition `cadd`, lemmas `dominates_caddl`, `Radon_Nikodym_cadd`

- in `lebesgue_integral.v`:
  + lemma `abse_integralP`

- in `classical_sets.v`:
  + lemma `set_cons1`
  + lemma `trivIset_bigcup`
  + definition `maximal_disjoint_subcollection`
  + lemma `ex_maximal_disjoint_subcollection`

- in `mathcomp_extra.v`:
  + lemma `leq_ltn_expn`

- in `lebesgue_measure.v`:
  + lemma `lebesgue_measurable_ball`
  + lemmas `measurable_closed_ball`, `lebesgue_measurable_closed_ball`

- in `normedtype.v`:
  + lemmas `ball0`, `ball_itv`, `closed_ball0`, `closed_ball_itv`
  + definitions `cpoint`, `radius`, `is_ball`
  + definition `scale_ball`, notation notation ``` *` ```
  + lemmas `sub_scale_ball`, `scale_ball1`, `sub1_scale_ball`
  + lemmas `ball_inj`, `radius0`, `cpoint_ball`, `radius_ball_num`,
    `radius_ball`, `is_ballP`, `is_ball_ball`, `scale_ball0`,
    `ballE`, `is_ball_closure`, `scale_ballE`, `cpoint_scale_ball`,
	`radius_scale_ball`
  + lemmas `vitali_lemma_finite`, `vitali_lemma_finite_cover`
  + definition `vitali_collection_partition`
  + lemmas `vitali_collection_partition_ub_gt0`,
    `ex_vitali_collection_partition`, `cover_vitali_collection_partition`,
	`disjoint_vitali_collection_partition`
  + lemma `separate_closed_ball_countable`
  + lemmas `vitali_lemma_infinite`, `vitali_lemma_infinite_cover`

- in `topology.v`:
  + lemmas `closure_eq0`, `separated_open_countable`

- in `exp.v`:
  + definition `expeR`
  + lemmas `expeR0`, `expeR_ge0`, `expeR_gt0`
  + lemmas `expeR_eq0`, `expeRD`, `expeR_ge1Dx`
  + lemmas `ltr_expeR`, `ler_expeR`, `expeR_inj`, `expeR_total`

- in `exp.v`:
  + lemmas `mulr_powRB1`, `fin_num_poweR`, `poweRN`, `poweR_lty`, `lty_poweRy`, `gt0_ler_poweR`

- in `mathcomp_extra.v`:
  + lemma `onemV`

- in `hoelder.v`:
  + lemmas `powR_Lnorm`, `minkowski`
  + lemma `expRM`

- in `measure.v`:
  + lemma `probability_setC`
- in `classical_sets.v`:
  + lemmas `mem_not_I`, `trivIsetT_bigcup`

- in `lebesgue_measure.v`:
  + definition `vitali_cover`
  + lemma `vitali_theorem`

- in `measure.v`:
  + lemma `measure_sigma_sub_additive_tail`
  + lemma `outer_measure_sigma_subadditive_tail`

- in `normedtype.v`:
  + lemma `open_subball`
  + lemma `closed_disjoint_closed_ball`
  + lemma `is_scale_ball`

- in `reals.v`:
  + lemmas `ceilN`, `floorN`

- in `sequences.v`:
  + lemma `nneseries_tail_cvg`

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
  
- in `probability.v`:
  + `markov` now uses `Num.nneg`
- in `lebesgue_integral.v`:
  + order of arguments in the lemma `le_abse_integral`

- in `lebesgue_measure.v`:
  + remove one argument of `lebesgue_regularity_inner_sup`

- in `normedtype.v`:
  + order of arguments of `squeeze_cvgr`

- moved from `derive.v` to `normedtype.v`:
  + lemmas `cvg_at_rightE`, `cvg_at_leftE`
  
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

- in `sequences.v`:
  + `ereal_nondecreasing_cvg` -> `ereal_nondecreasing_cvgn`
  + `ereal_nondecreasing_is_cvg` -> `ereal_nondecreasing_is_cvgn`
  + `ereal_nonincreasing_cvg` -> `ereal_nonincreasing_cvgn`
  + `ereal_nonincreasing_is_cvg` -> `ereal_nonincreasing_is_cvgn`
  + `ereal_nondecreasing_opp` -> `ereal_nondecreasing_oppn`
  + `nonincreasing_cvg_ge` -> `nonincreasing_cvgn_ge`
  + `nondecreasing_cvg_le` -> `nondecreasing_cvgn_le`
  + `nonincreasing_cvg` -> `nonincreasing_cvgn`
  + `nondecreasing_cvg` -> `nondecreasing_cvgn`
  + `nonincreasing_is_cvg` -> `nonincreasing_is_cvgn`
  + `nondecreasing_is_cvg` -> `nondecreasing_is_cvgn`
  + `near_nonincreasing_is_cvg` -> `near_nonincreasing_is_cvgn`
  + `near_nondecreasing_is_cvg` -> `near_nondecreasing_is_cvgn`
  + `nondecreasing_dvg_lt` -> `nondecreasing_dvgn_lt`

### Generalized

- in `topology.v`:
  + `ball_filter` generalized to `realDomainType`

- in `lebesgue_integral.v`:
  + weaken an hypothesis of `integral_ae_eq`
- in `classical_sets.v`:
  + `set_nil` generalized to `eqType`

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
