# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemmas `continuous_subspaceT`, `subspaceT_continuous`
- in `constructive_ereal.v`
  + lemmas `fine_le`, `fine_lt`, `fine_abse`, `abse_fin_num`
- in `lebesgue_integral.v`
  + lemmas `integral_fune_lt_pinfty`, `integral_fune_fin_num`
- in `topology.v`
  + lemma `weak_subspace_open`
  + lemma `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`, `weak_ent_split`,
      `weak_ent_nbhs`
  + definition `map_pair`, `weak_ent`, `weak_uniform_mixin`, `weak_uniformType`
  + lemma `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
      `sup_ent_nbhs`
  + definition `sup_ent`, `sup_uniform_mixin`, `sup_uniformType`
  + definition `product_uniformType`
  + lemma `uniform_entourage`
  + definition `weak_ball`, `weak_pseudoMetricType`
  + lemma `weak_ballE`
  + lemma `finI_from_countable`
  + definition `countable_uniformity`
  + lemmas `countable_uniformityP`, `countable_sup_ent`,
     `countable_uniformity_metric`
- in `cardinality.v`
  + lemmas `eq_card1`, `card_set1`, `card_eqSP`, `countable_n_subset`,
     `countable_finite_subset`, `eq_card_fset_subset`, `fset_subset_countable`
- in `classical_sets.v`
  + lemmas `IIDn`, `IISl`
- in `mathcomp_extra.v`
  + lemma `lez_abs2n`
- in `constructive_ereal.v`:
  + lemmas `gte_addl`, `gte_addr`
  + lemmas `gte_daddl`, `gte_daddr`
  + lemma `lte_spadder`, `lte_spaddre`
  + lemma `lte_spdadder`
- in `constructive_ereal.v`:
  + lemma `sum_fine`
- in `topology.v`
  + lemmas `entourage_invI`, `split_ent_subset`
  + definition `countable_uniform_pseudoMetricType_mixin`
- in `reals.v`:
  + lemma `floor0`
- in `classical_sets.v`:
  + canonical `unit_pointedType`
- in `measure.v`:
  + definition `finite_measure`
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`
  + structures `sigma_finite_additive_measure` and `sigma_finite_measure`

- in file `topology.v`,
  + new definition `perfect_set`.
  + new lemmas `perfectTP`, `perfect_prod`, and `perfect_diagonal`.
- in `constructive_ereal.v`:
  + lemmas `EFin_sum_fine`, `sumeN`
  + lemmas `adde_defDr`, `adde_def_sum`, `fin_num_sumeN`
  + lemma `fin_num_adde_defr`, `adde_defN`

- in `constructive_ereal.v`:
  + lemma `oppe_inj`

- in `mathcomp_extra.v`:
  + lemma `add_onemK`
  + function `swap`
- in `classical_sets.v`:
  + lemmas `setT0`, `set_unit`, `set_bool`
  + lemmas `xsection_preimage_snd`, `ysection_preimage_fst`
- in `exp.v`:
  + lemma `expR_ge0`
- in `measure.v`
  + lemmas `measurable_curry`, `measurable_fun_fst`, `measurable_fun_snd`,
    `measurable_fun_swap`, `measurable_fun_pair`, `measurable_fun_if_pair`
  + lemmas `dirac0`, `diracT`
  + lemma `finite_measure_sigma_finite`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_opp`
- in `lebesgue_integral.v`
  + lemmas `integral0_eq`, `fubini_tonelli`
  + product measures now take `{measure _ -> _}` arguments and their
    theory quantifies over a `{sigma_finite_measure _ -> _}`.

- in `classical_sets.v`:
  + lemma `trivIset_mkcond`
- in `numfun.v`:
  + lemmas `xsection_indic`, `ysection_indic`
- in `classical_sets.v`:
  + lemmas `xsectionI`, `ysectionI`
- in `lebesgue_integral.v`:
  + notations `\x`, `\x^` for `product_measure1` and `product_measure2`

- in `constructive_ereal.v`:
  + lemmas `expeS`, `fin_numX`

- in `functions.v`:
  + lemma `countable_bijP`
  + lemma `patchE`

- in `constructive_ereal.v`:
  + lemmas `adde_def_doppeD`, `adde_def_doppeB`
  + lemma `fin_num_sume_distrr`
- in `classical_sets.v`:
  + lemma `coverE`

- in file `topology.v`,
  + new definitions `quotient_topology`, and `quotient_open`.
  + new lemmas `pi_continuous`, `quotient_continuous`, and
    `repr_comp_continuous`.

- in file `boolp.v`,
  + new lemma `forallp_asboolPn2`.
- in file `classical_sets.v`,
  + new lemma `preimage_range`.
- in file `topology.v`,
  + new definitions `hausdorff_accessible`, `separate_points_from_closed`, and 
    `join_product`.
  + new lemmas `weak_sep_cvg`, `weak_sep_nbhsE`, `weak_sep_openE`, 
    `join_product_continuous`, `join_product_open`, `join_product_inj`, and 
    `join_product_weak`. 

### Changed

- in `fsbigop.v`:
  + implicits of `eq_fsbigr`
- move from `lebesgue_integral.v` to `classical_sets.v`
  + lemmas `trivIset_preimage1`, `trivIset_preimage1_in`
- move from `lebesgue_integral.v` to `numfun.v`
  + lemmas `fimfunE`, `fimfunEord`, factory `FiniteDecomp`
  + lemmas `fimfun_mulr_closed`
  + canonicals `fimfun_mul`, `fimfun_ring`, `fimfun_ringType`
  + defintion `fimfun_ringMixin`
  + lemmas `fimfunM`, `fimfun1`, `fimfun_prod`, `fimfunX`,
    `indic_fimfun_subproof`.
  + definitions `indic_fimfun`, `scale_fimfun`, `fimfun_comRingMixin`
  + canonical `fimfun_comRingType`
  + lemma `max_fimfun_subproof`
  + mixin `IsNonNegFun`, structure `NonNegFun`, notation `{nnfun _ >-> _}`

### Renamed

- in `measurable.v`:
  + `measurable_fun_comp` -> `measurable_funT_comp`
- in `numfun.v`:
  + `IsNonNegFun` -> `isNonNegFun`
- in `lebesgue_integral.v`:
  + `IsMeasurableFunP` -> `isMeasurableFun`
- in `measure.v`:
  + `{additive_measure _ -> _}` -> `{content _ -> _}`
  + `isAdditiveMeasure` -> `isContent`
  + `AdditiveMeasure` -> `Content`
  + `additive_measure` -> `content`
  + `additive_measure_snum_subproof` -> `content_snum_subproof`
  + `additive_measure_snum` -> `content_snum`
  + `SigmaFiniteAdditiveMeasure` -> `SigmaFiniteContent`
  + `sigma_finite_additive_measure` -> `sigma_finite_content`
  + `{sigma_finite_additive_measure _ -> _}` -> `{sigma_finite_content _ -> _}`
- in `constructive_ereal.v`:
  + `fin_num_adde_def` -> `fin_num_adde_defl`
  + `oppeD` -> `fin_num_oppeD`
  + `oppeB` -> `fin_num_oppeB`
  + `doppeD` -> `fin_num_doppeD`
  + `doppeB` -> `fin_num_doppeB`
- in `topology.v`:
  + `finSubCover` -> `finite_subset_cover`

### Generalized

- in `esum.v`:
  + lemma `esum_esum`
- in `measure.v`
  + lemma `measurable_fun_comp`
- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`
- in `measure.v`:
  + lemma `measure_bigcup` generalized,
- in `classical_sets.v`:
  + `xsection_preimage_snd`, `ysection_preimage_fst`
- in `constructive_ereal.v`:
  + `oppeD`, `oppeB`

### Deprecated

### Removed

- in `esum.v`:
  + lemma `fsbig_esum`

### Infrastructure

### Misc
