# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + definition `powerset_filter_from`
  + globals `powerset_filter_from_filter`, 
  + lemmas `near_small_set`, `small_set_sub`, `near_powerset_filter_fromP`
  + lemmas `withinET`, `closureEcvg`, `entourage_sym`, `fam_nbhs`
  + definition `near_covering`
  + lemma `compact_near_coveringP`
  + lemma `continuous_localP`, `equicontinuous_subset_id`
  + lemmas `ptws_cvg_entourage`, `equicontinuous_closure`, `ptws_compact_cvg`
    `ptws_compact_closed`, `ascoli_forward`
  + lemmas `precompact_pointwise_precompact`, `precompact_equicontinuous`,
    `ascoli_theorem`
- in file `classical_sets.v`
  + lemma `set_bool`
- in file `topology.v`:
  + definition `principal_filter` `discrete_space`
  + lemma `principal_filterP`, `principal_filter_proper`, 
      `principa;_filter_ultra`
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
- in file `normedtype.v`:
  + definition `bigcup_ointsub`
  + lemmas `bigcup_ointsub0`, `open_bigcup_ointsub`, `is_interval_bigcup_ointsub`,
    `bigcup_ointsub_sub`, `open_bigcup_rat`
  + lemmas `mulrl_continuous` and `mulrr_continuous`.
- in file `lebesgue_measure.v`:
  + lemmas `is_interval_measurable`, `open_measurable`, `continuous_measurable_fun`
- in `classical_sets.v`:
  + lemma `preimage_setT`
- in `ereal.v`:
  + definition `expe` with notation `^+`
  + definition `enatmul` with notation `*+` (scope `%E`)
  + definition `ednatmul` with notation `*+` (scope `%dE`)
  + lemmas `fineM`, `enatmul_pinfty`, `enatmul_ninfty`, `EFin_natmul`, `mule2n`, `expe2`,
    `mule_natl`
  + lemmas `ednatmul_pinfty`, `ednatmul_ninfty`, `EFin_dnatmul`, `dmule2n`, `ednatmulE`,
    `dmule_natl`
  + lemmas `sum_fin_num`, `sum_fin_numP`
- in `esum.v`:
  + lemma `esum_set1`
- in `ereal.v`:
  + lemmas `oppeB`, `doppeB`, `fineB`, `dfineB`
- in file `mathcomp_extra.v`:
  + lemma `card_fset_sum1`
- in file `classical_sets.v`:
  + lemmas `setI_II` and `setU_II`
- in file `cardinality.v`:
  + lemma `fset_set_image`, `card_fset_set`, `geq_card_fset_set`,
    `leq_card_fset_set`, `infinite_set_fset`, `infinite_set_fsetP` and
    `fcard_eq`.
  + notations `{posnum \bar R}` and `{nonneg \bar R}`
  + notations `%:pos` and `%:nng` in `ereal_dual_scope` and `ereal_scope`
  + variants `posnume_spec` and `nonnege_spec`
  + definitions `posnume`, `nonnege`, `abse_reality_subdef`,
    `ereal_sup_reality_subdef`, `ereal_inf_reality_subdef`
  + lemmas `ereal_comparable`, `pinfty_snum_subproof`, `ninfty_snum_subproof`,
    `EFin_snum_subproof`, `fine_snum_subproof`, `oppe_snum_subproof`,
    `adde_snum_subproof`, `dadde_snum_subproof`, `mule_snum_subproof`,
    `abse_reality_subdef`, `abse_snum_subproof`, `ereal_sup_snum_subproof`,
    `ereal_inf_snum_subproof`, `num_abse_eq0`, `num_lee_maxr`, `num_lee_maxl`,
    `num_lee_minr`, `num_lee_minl`, `num_lte_maxr`, `num_lte_maxl`,
    `num_lte_minr`, `num_lte_minl`, `num_abs_le`, `num_abs_lt`,
    `posnumeP`, `nonnegeP`
  + signed instances `pinfty_snum`, `ninfty_snum`, `EFin_snum`, `fine_snum`,
    `oppe_snum`, `adde_snum`, `dadde_snum`, `mule_snum`, `abse_snum`,
    `ereal_sup_snum`, `ereal_inf_snum`
- in `topology.v`:
  + Definition `powerset_filter_from`
  + globals `powerset_filter_from_filter`, 
  + lemmas `near_small_set`, `small_set_sub`
  + lemmas `withinET`, `closureEcvg`, `entourage_sym`, `fam_nbhs`
  + generalize `cluster_cvgE`, `ptws_cvg_compact_family`
  + lemma `near_compact_covering`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index 
  + lemmas `ptws_cvg_entourage`, `equicontinuous_closure`, `ptws_compact_cvg`
    `ptws_compact_closed`, `ascoli_forward`, `compact_equicontinuous`
- in file `ereal.v`:
  + lemma `abse1`
- in file `sequences.v`:
  + lemmas `nneseriesrM`, `ereal_series_cond`, `ereal_series`, `nneseries_split`
  + lemmas `lee_nneseries`
- in file `esum.v`:
  + lemma `nnseries_interchange`
- in file `ereal.v`:
  + lemma `ltninfty_adde_def`
- in file `lebesgue_measure.v`:
  + lemma `emeasurable_funN`
- in file `measure.v`:
  + definition `pushforward` and canonical `pushforward_measure`
  + definition `dirac` with notation `\d_` and canonical `dirac_measure`
  + lemmas `finite_card_dirac`, `infinite_card_dirac`
- in file `lebesgue_integral.v`:
  + lemmas `integralM_indic`, `integralM_indic_nnsfun`, `integral_dirac`
- in file `measure.v`:
  + lemma `eq_measure`
  + definition `msum`
  + definition `mzero`
  + definition `measure_add` and lemma `measure_addE`
  + definition `mseries`
- in file `lebesgue_integral.v`:
  + lemma `integral_measure_zero`
  + lemma `eq_measure_integral`
  + mixins `isAdditiveMeasure`, `isMeasure0`, `isMeasure`, `isOuterMeasure`
  + structures `AdditiveMeasure`, `Measure`, `OuterMeasure`
  + notations `additive_measure`, `measure`, `outer_measure`
  + definition `mrestr`
- in file `classical_sets.v`:
  + lemma `trivIset_set0`
- in `measure.v`:
  + lemmas `additive_measure_snum_subproof`, `measure_snum_subproof`
  + canonicals `additive_measure_snum`, `measure_snum`

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
- in `esum.v`:
  + remove one hypothesis in lemmas `reindex_esum`, `esum_image`
- moved from `lebesgue_integral.v` to `lebesgue_measure.v` and generalized
  + hint `measurable_set1`/`emeasurable_set1`
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

### Renamed

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
- in `mathcomp_extra.v`:
  + lemmas `natr_absz`, `ge_pinfty`, `le_ninfty`, `gt_pinfty`,
    `lt_ninfty`
- in `classical_sets.v`:
  + notation `[set of _]`
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