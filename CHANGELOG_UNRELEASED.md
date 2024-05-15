# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `bigcup_recl`

- in `sequences.v`:
  + lemma `nneseries_recl`

- in file `mathcomp_extra.v`:
  + module `Order`
    * definitions `disp_t`, `default_display`

- in `measure.v`:
  + definition `subset_sigma_subadditive`
  + factory `isSubsetOuterMeasure`

- in file `classical_sets.v`
  + notations `\bigcup_(i >= n) F i` and `\bigcap_(i >= n) F i`
  + lemmas `bigcup_addn`, `bigcap_addn`

- in file `sequences.v`
  + lemma `nneseries_addn`
- in `lebesgue_integral.v`:
  + lemmas `integrableMl`, `integrableMr`

- in `realfun.v`
  + lemmas `total_variation_nondecreasing`, `total_variation_bounded_variation`
- new file `theories/all_analysis.v`

- in `normedtype.v`:
  + lemma `not_near_at_leftP`
- in `classical_sets.v`:
  + lemmas `setD_bigcup`, `nat_nonempty`
  + hint `nat_nonempty`

- in `measure.v`:
  + structure `SigmaRing`, notation `sigmaRingType`
  + factory `isSigmaRing`
  + lemma `bigcap_measurable` for `sigmaRingType`
  + lemma `setDI_semi_setD_closed`

- in `lebesgue_measure.v`:
  + lemma `measurable_fun_ler`

- in `measure.v`:
  + lemma `measurable_and`

- in `signed.v`:
  + lemma `onem_nonneg_proof`, definition `onem_nonneg`

- in `esum.v`:
  + lemma `nneseries_sum_bigcup`

- in `lebesgue_measurable.v`:
  + lemmas `measurable_natmul`, `measurable_fun_pow`

- in `probability.v`:
  + definition `bernoulli_pmf`
  + lemmas `bernoulli_pmf_ge0`, `bernoulli_pmf1`, `measurable_bernoulli_pmf`
  + definition  `bernoulli` (equipped with the `probability` structure)
  + lemmas `bernoulli_dirac`, `bernoulliE`, `integral_bernoulli`, `measurable_bernoulli`,
    `measurable_bernoulli2`
  + definition `binomial_pmf`
  + lemmas `binomial_pmf_ge0`, `measurable_binomial_pmf`
  + definitions `binomial_prob` (equipped with the `probability` structure), `bin_prob`
  + lemmas `bin_prob0`, `bin_prob1`, `binomial_msum`, `binomial_probE`, `integral_binomial`,
    `integral_binomial_prob`, `measurable_binomial_prob`
  + definition `uniform_pdf`
  + lemmas `measurable_uniform_pdf`, `integral_uniform_pdf`, `integral_uniform_pdf1`
  + definition `uniform_prob` (equipped with the `probability` structure)
  + lemmas `dominates_uniform_prob`, `integral_uniform`

- in `measure.v`:
  + lemma `measurableID`

- in `mathcomp_extra.v`:
  + lemma `Pos_to_natE`

- in `Rstruct.v`:
  + lemma `IZRposE`

### Changed

- in `forms.v`:
  + notation ``` u ``_ _ ```

- in `trigo.v`:
  + definitions `sin`, `cos`, `acos`, `asin`, `atan` are now HB.locked
- in `sequences.v`:
  + definition `expR` is now HB.locked

- in `measure.v`:
  + change the hypothesis of `measurable_fun_bool`
  + mixin `AlgebraOfSets_isMeasurable` renamed to `hasCountableUnion`
  + mixin `AlgebraOfSets_isMeasurable` renamed to `hasMeasurableCountableUnion`
    and made to inherit from `SemiRingOfSets`

### Renamed

- in `constructive_ereal.v`:
  + `gee_pmull` -> `gee_pMl`
  + `gee_addl` -> `geeDl`
  + `gee_addr` -> `geeDr`
  + `gte_addl` -> `gteDl`
  + `gte_addr` -> `gteDr`
  + `lte_subl_addr` -> `lteBlDr`
  + `lte_subl_addl` -> `lteBlDl`
  + `lte_subr_addr` -> `lteBrDr`
  + `lte_subr_addl` -> `lteBrDl`
  + `lee_subl_addr` -> `leeBlDr`
  + `lee_subl_addl` -> `leeBlDl`
  + `lee_subr_addr` -> `leeBrDr`
  + `lee_subr_addl` -> `leeBrDl`

- in `measure.v`:
  + `sub_additive` -> `subadditive`
  + `sigma_sub_additive` -> `measurable_subset_sigma_subadditive`
  + `content_sub_additive` -> `content_subadditive`
  + `ring_sigma_sub_additive` -> `ring_sigma_subadditive`
  + `Content_SubSigmaAdditive_isMeasure` -> `Content_SigmaSubAdditive_isMeasure`
  + `measure_sigma_sub_additive` -> `measure_sigma_subadditive`
  + `measure_sigma_sub_additive_tail` -> `measure_sigma_subadditive_tail`

- in `classical_sets.v`:
  + `notin_set` -> `notin_setE`

- in `signed.v`:
  + `num_le_maxr` -> `num_le_max`
  + `num_le_maxl` -> `num_ge_max`
  + `num_le_minr` -> `num_le_min`
  + `num_le_minl` -> `num_ge_min`
  + `num_lt_maxr` -> `num_lt_max`
  + `num_lt_maxl` -> `num_gt_max`
  + `num_lt_minr` -> `num_lt_min`
  + `num_lt_minl` -> `num_gt_min`

- in `constructive_ereal.v`:
  + `num_lee_maxr` -> `num_lee_max`
  + `num_lee_maxl` -> `num_gee_max`
  + `num_lee_minr` -> `num_lee_min`
  + `num_lee_minl` -> `num_gee_min`
  + `num_lte_maxr` -> `num_lte_max`
  + `num_lte_maxl` -> `num_gte_max`
  + `num_lte_minr` -> `num_lte_min`
  + `num_lte_minl` -> `num_gte_min`
- in `measure.v`:
  + `bigcap_measurable` -> `bigcap_measurableType`

- in `lebesgue_integral.v`:
  + `integral_measure_add` -> `ge0_integral_measure_add`
  + `integral_pushforward` -> `ge0_integral_pushforward`

### Generalized

- in `Rstruct.v`:
  + lemmas `RinvE`, `RdivE`

- in `constructive_ereal.v`:
  + `gee_pMl` (was `gee_pmull`)

- in `sequences.v`:
  + lemmas `eseries0`, `nneseries_split`

- in `lebesgue_integral.v`:
  + lemma `ge0_integral_bigcup`
- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2` (from `semiRingOfSetType` to `Type`)
  + lemmas `caratheodory_measurable_mu_ext`, `measurableM`, `measure_dominates_trans`, `ess_sup_ge0`
    definitions `preimage_classes`, `measure_dominates`, `ess_sup`
	(from `measurableType` to `semiRingOfSetsType`)
  + lemmas ` measurable_prod_measurableType`, `measurable_prod_g_measurableTypeR` (from `measurableType` to `algebraOfSetsType`)

- in `lebesgue_integral.v`:
  + lemma `ge0_emeasurable_fun_sum`

- in `probability.v`:
  + lemma `markov`
- in `measure.v`:
  + from `measurableType` to `sigmaRingType`
    * lemmas `bigcup_measurable`, `bigcapT_measurable`
	* definition `measurable_fun`
	* lemmas `measurable_id`, `measurable_comp`, `eq_measurable_fun`, `measurable_cst`, `measurable_fun_bigcup`, `measurable_funU`, `measurable_funS`, `measurable_fun_if`
	* lemmas `semi_sigma_additiveE`, `sigma_additive_is_additive`, `measure_sigma_additive`
	* definitions `pushforward`, `dirac`
	* lemmas `diracE`, `dirac0`, `diracT`, `finite_card_sum`, `finite_card_dirac`, `infinite_card_dirac`
	* definitions `msum`, `measure_add`, `mscale`, `mseries`, `mrestr`
	* lemmas `msum_mzero`, `measure_addE`
	* definition `sfinite_measure`
	* mixin `isSFinite`, structure `SFiniteMeasure`
	* structure `FiniteMeasure`
	* factory `Measure_isSFinite`
	* lemma `negligible_bigcup`
	* definition `ae_eq`
	* lemmas `ae_eq0`, `ae_eq_comp`, `ae_eq_funeposneg`, `ae_eq_refl`, `ae_eq_sym`,
	  `ae_eq_trans`, `ae_eq_sub`, `ae_eq_mul2r`, `ae_eq_mul2l`, `ae_eq_mul1l`,
	  `ae_eq_abse`
  + from `measurableType` to `sigmaRingType` and from `realType` to `realFieldType`
	* definition `mzero`
  + from `realType` to `realFieldType`:
    * lemma `sigma_finite_mzero`

- in `lebesgue_integral.v`:
  + from `measurableType` to `sigmaRingType`
    * mixin `isMeasurableFun` 
    * structure `SimpleFun`
	* structure `NonNegSimpleFun`
	* sections `fimfun_bin`, `mfun_pred`, `sfun_pred`, `simple_bounded`
	* lemmas `nnfun_muleindic_ge0`, `mulemu_ge0`, `nnsfun_mulemu_ge0`
	* section `sintegral_lemmas`
	* lemma `eq_sintegral`
	* section `sintegralrM`

### Deprecated

- in `classical_sets.v`:
  + `notin_set` (use `notin_setE` instead)

### Removed

- in `lebesgue_integral.v`:
  + `integrablerM`, `integrableMr` (were deprecated since version 0.6.4)

- in `measure.v`:
  + lemmas `prod_salgebra_set0`, `prod_salgebra_setC`, `prod_salgebra_bigcup`
    (use `measurable0`, `measurableC`, `measurable_bigcup` instead)
- in `derive.v`:
  + definition `mulr_rev`
  + canonical `rev_mulr`
  + lemmas `mulr_is_linear`, `mulr_rev_is_linear`

- in `forms.v`
  + canonical `rev_mulmx`
  + structure `revop`

- in `reals.v`
  + lemma `inf_lower_bound` (use `inf_lb` instead)

### Infrastructure

### Misc
