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

### Renamed

- in `lebesgue_integral.v`:
  + `integralK` -> `integralrM`

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

### Infrastructure

### Misc