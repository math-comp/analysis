# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + definition `near_covering`
  + lemma `compact_near_coveringP`
  + lemma `continuous_localP`, `equicontinuous_subset_id`
  + lemmas `precompact_pointwise_precompact`, `precompact_equicontinuous`,
    `Ascoli`
- in file `classical_sets.v`
  + lemma `set_bool`
- in file `topology.v`:
  + definition `principal_filter` `discrete_space`
  + lemma `principal_filterP`, `principal_filter_proper`, 
      `principal_filter_ultra`
  + canonical `bool_discrete_filter`
  + lemma `compactU`
  + lemma `discrete_sing`, `discrete_nbhs`, `discrete_open`, `discrete_set1`,
      `discrete_closed`, `discrete_cvg`, `discrete_hausdorff`
  + canonical `bool_discrete_topology`
  + definition `discrete_topological_mixin`
  + lemma `discrete_bool`, `bool_compact`
- in `reals.v`:
  + lemma `floor_natz`
- in file `topology.v`:
  + definition `frechet_filter`, instances `frechet_properfilter`, and `frechet_properfilter_nat`
- in `Rstruct.v`:
  + lemmas `Rsupremums_neq0`, `Rsup_isLub`, `Rsup_ub`
- in `classical_sets.v`:
  + lemma `supremum_out`
  + definition `isLub`
  + lemma `supremum1`
- in `reals.v`:
  + lemma `opp_set_eq0`, `ubound0`, `lboundT`
- in `lebesgue_integral.v`:
  + lemma `integrable0`
- in file `lebesgue_integral.v`:
  + mixins `isAdditiveMeasure`, `isMeasure0`, `isMeasure`, `isOuterMeasure`
  + structures `AdditiveMeasure`, `Measure`, `OuterMeasure`
  + notations `additive_measure`, `measure`, `outer_measure`
  + definition `mrestr`
- in file `classical_sets.v`:
  + lemma `trivIset_set0`
- in `measure.v`:
  + lemmas `additive_measure_snum_subproof`, `measure_snum_subproof`
  + canonicals `additive_measure_snum`, `measure_snum`
  + definition `mscale`
- in `lebesgue_measure.v`:
  + lemma `diracE`
- in file `cardinality.v`:
  + lemmas `trivIset_sum_card`, `fset_set_sub`, `fset_set_set0`
- in file `sequences.v`:
  + lemmas `nat_dvg_real`, `nat_cvgPpinfty`, `nat_nondecreasing_is_cvg`
  + definition `nseries`, lemmas `le_nseries`, `cvg_nseries_near`, `dvg_nseries`
- in file `measure.v`:
  + definition `restr`
  + definition `counting`, canonical `measure_counting`
- in file `measure.v`:
  + definition `discrete_measurable`, instantiated as a `measurableType`
  + lemma `sigma_finite_counting`
  + lemma `msum_mzero`
- in `lebesgue_integral.v`:
  + lemmas `integral_measure_sum_nnsfun`, `integral_measure_add_nnsfun`
- in file `lebesgue_integral.v`:
  + lemmas `ge0_integral_measure_sum`, `integral_measure_add`, `integral_measure_series_nnsfun`,
    `ge0_integral_measure_series`
- in file `ereal.v`:
  + lemma `fin_num_abs`
- in file `esum.v`:
  + definition `summable`
  + lemmas `summable_pinfty`, `summableE`, `summableD`, `summableN`, `summableB`,
    `summable_funepos`, `summable_funeneg`
  + lemmas `summable_fine_sum`, `summable_cvg`, `summable_nneseries_lim`,
    `summable_nnseries`, `summable_nneseries_esum`, `esumB`
- in file `lebesgue_integral.v`:
  + lemmas `integrable_neg_fin_num`, `integrable_pos_fin_num`
  + lemma `integral_measure_series`
  + lemmas `counting_dirac`, `summable_integral_dirac`, `integral_count`
  + lemmas `integrable_abse`, `integrable_summable`, `integral_bigcup`
- in `trigo.v`:
  + lemmas `cos1_gt0`, `pi_ge2`
  + lemmas `pihalf_ge1`, `pihalf_lt2`
- in `measure.v`:
  + inductive `measure_display`
  + notation `_.-sigma`, `_.-sigma.-measurable`,
             `_.-ring`, `_.-ring.-measurable`,
             `_.-cara`, `_.-cara.-measurable`,
             `_.-caratheodory`,
             `_.-prod`. `_.-prod.-measurable`
  + notation `_.-measurable`
- in `lebesgue_measure.v`:
  + notation `_.-ocitv`
  + definition `ocitv_display`

### Changed

- in `topology.v`:
  + generalize `cluster_cvgE`, `fam_cvgE`, `ptws_cvg_compact_family`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index
- in `Rstruct.v`:
  + statement of lemma `completeness'`, renamed to `Rcondcomplete`
  + statement of lemma `real_sup_adherent`
- in `ereal.v`:
  + statements of lemmas `ub_ereal_sup_adherent`, `lb_ereal_inf_adherent`
- in `reals.v`:
  + definition `sup`
  + statements of lemmas `sup_adherent`, `inf_adherent`
- in `sequences.v`:
  + generalize `eq_nneseries`, `nneseries0`
- in `mathcomp_extra.v`:
  + generalize `card_fset_sum1`
- in `lebesgue_integral.v`:
  + change the notation `\int_`
- in `measure.v`:
  + `measure0` is now a lemma
- in `lebesgue_integral.v`:
  + `product_measure1` takes a proof that the second measure is sigma-finite
  + `product_measure2` takes a proof that the first measure is sigma-finite
- in `lebesgue_integral.v`:
  + definitions `integral` and `integrable` now take a function instead of a measure
  + remove one space in notation `\d_`
  + generalize `nondecreasing_series`
- in `trigo.v`:
  + lemma `cos_exists`
- in `set_interval.v`:
  + generalize to numDomainType:
    * `mem_1B_itvcc`, `conv`, `conv_id`, `convEl`, `convEr`,
    `conv10`, `conv0`, conv1`, `conv_sym`, `conv_flat`, `leW_conv`,
    `factor`, `leW_factor`, `factor_flat`, `factorl`, `ndconv`,
    `ndconvE`
  + generalize to numFieldType
    * `factorr`, `factorK`, `convK`, `conv_inj`, `factor_inj`,
    `conv_bij`, `factor_bij`, `le_conv`, `le_factor`, `lt_conv`,
    `lt_factor`, `conv_itv_bij`, `factor_itv_bij`, `mem_conv_itv`,
    `mem_conv_itvcc`, `range_conv`, `range_factor`
  + generalize to realFieldType:
    * `mem_factor_itv`

### Renamed

- in `lebesgue_integral.v`:
  + `integralK` -> `integralrM`
- in `trigo.v`:
  + `cos_pihalf_uniq` -> `cos_02_uniq`
- in `measure.v`:
  + `sigma_algebraD` -> `sigma_algebraCD`
  + `g_measurable` -> `salgebraType`
  + `g_measurable_eqType` -> `salgebraType_eqType`
  + `g_measurable_choiceType` -> `salgebraType_choiceType`
  + `g_measurable_ptType` -> `salgebraType_ptType`
- in `lebesgue_measure.v`:
  + `itvs` -> `ocitv_type`

### Removed

- `has_sup1`, `has_inf1` moved from `reals.v` to `classical_sets.v`
- in `reals.v`:
  + type generalization of `has_supPn`
- in `classical_sets.v`:
  + `supremums_set1` -> `supremums1`
  + `infimums_set1` -> `infimums1`
- in `Rstruct.v`:
  + definition `real_sup`
  + lemma `real_sup_is_lub`, `real_sup_ub`, `real_sup_out`
- in `reals.v`:
  + field `sup` from `mixin_of` in module `Real`
- in `measure.v`:
  + notations `[additive_measure _ -> _]`, `[measure _ -> _]`, `[outer_measure _ -> _ ]`,
  + lemma `measure_is_additive_measure`
  + definitions `caratheodory_measure_mixin`, `caratheodory_measure`
  + coercions `measure_to_nadditive_measure`, `measure_additive_measure`
  + canonicals `measure_additive_measure`, `set_ring_measure`,
    `outer_measure_of_measure`, `Hahn_ext_measure`
  + lemma `Rmu0`
  + lemma `measure_restrE`
- in `measure.v`, several constructs now take a parameter of type `measure_display`
- in `lebesgue_integral.v`, constructs with a parameter `measurableType` now
  take an addititional parameter of type `measure_display`
- in `measure.v`:
  + definition `g_measurableType`
  + notation `mu.-measurable`

### Infrastructure

### Misc