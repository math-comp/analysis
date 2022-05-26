# Changelog (unreleased)

## [Unreleased]

### Added

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
  + definition `msum` and canonical `measure_sum'`
  + definition `mzero` and canonical `measure_zero'`
  + definition `measure_add` and lemma `measure_addE`
  + definition `mseries` and canonical `measure_series'`
- in file `lebesgue_integral.v`:
  + lemma `integral_measure_zero`
  + lemma `eq_measure_integral`
- in file `classical_sets.v`:
  + lemma `bigsetU_bigcup`
- in file `numfun.v`:
  + lemma `restrict_lee`
- in file `lebesgue_integral.v`:
  + lemmas `integral_set0`, `ge0_integral_bigsetU`, `ge0_integral_bigcup`
- in file `lebesgue_measure.v`:
  + lemmas `itv_bnd_open_bigcup`, `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`
  + lemma `lebesgue_measure_set1`
  + lemma `lebesgue_measure_itv`

### Changed

- in `esumv`:
  + remove one hypothesis in lemmas `reindex_esum`, `esum_image`
- moved from `lebesgue_integral.v` to `lebesgue_measure.v` and generalized
  + hint `measurable_set1`/`emeasurable_set1`
- in `sequences.v`:
  + generalize `eq_nneseries`, `nneseries0`
- in `mathcomp_extra.v`:
  + generalize `card_fset_sum1`
- in `lebesgue_integral.v`:
  + change the notation `\int_`

### Renamed

- in `ereal.v`:
  + `num_abs_le` -> `num_abse_le`
  + `num_abs_lt` -> `num_abse_lt`
  + `addooe` -> `addye`
  + `addeoo` -> `addey`
  + `mule_ninfty_pinfty` -> `mulNyy`
  + `mule_pinfty_ninfty` -> `mulyNy`
  + `mule_pinfty_pinfty` -> `mulyy`
  + `mule_ninfty_ninfty` -> `mulNyNy`
  + `lte_0_pinfty` -> `lt0y`
  + `lte_ninfty_0` -> `ltNy0`
  + `lee_0_pinfty` -> `le0y`
  + `lee_ninfty_0` -> `leNy0`
  + `lte_pinfty` -> `ltey`
  + `lte_ninfty` -> `ltNye`
  + `lee_pinfty` -> `leey`
  + `lee_ninfty` -> `leNye`
  + `mulrpinfty_real` -> `real_mulry`
  + `mulpinftyr_real` -> `real_mulyr`
  + `mulrninfty_real` -> `real_mulrNy`
  + `mulninftyr_real` -> `real_mulNyr`
  + `mulrpinfty` -> `mulry`
  + `mulpinftyr` -> `mulyr`
  + `mulrninfty` -> `mulrNy`
  + `mulninftyr` -> `mulNyr`
  + `gt0_mulpinfty` -> `gt0_mulye`
  + `lt0_mulpinfty` -> `lt0_mulye`
  + `gt0_mulninfty` -> `gt0_mulNye`
  + `lt0_mulninfty` -> `lt0_mulNye`
  + `maxe_pinftyl` -> `maxye`
  + `maxe_pinftyr` -> `maxey`
  + `maxe_ninftyl` -> `maxNye`
  + `maxe_ninftyr` -> `maxeNy`
  + `mine_ninftyl` -> `minNye`
  + `mine_ninftyr` -> `mineNy`
  + `mine_pinftyl` -> `minye`
  + `mine_pinftyr` -> `miney`
  + `mulrinfty_real` -> `real_mulr_infty`
  + `mulrinfty` -> `mulr_infty`
- in `realfun.v`:
  + `exp_continuous` -> `exprn_continuous`
- in `sequences.v`:
  + `ereal_pseriesD` -> `nneseriesD`
  + `ereal_pseries0` -> `nneseries0`
  + `ereal_pseries_pred0` -> `nneseries_pred0`
  + `eq_ereal_pseries` -> `eq_nneseries`
  + `ereal_pseries_sum_nat` -> `nneseries_sum_nat`
  + `ereal_pseries_sum` -> `nneseries_sum`
  + `ereal_pseries_mkcond` -> `nneseries_mkcond`
  + `ereal_nneg_series_lim_ge` -> `nneseries_lim_ge`
  + `is_cvg_ereal_nneg_series_cond` -> `is_cvg_nneseries_cond`
  + `is_cvg_ereal_nneg_series` -> `is_cvg_nneseries`
  + `ereal_nneg_series_lim_ge0` -> `nneseries_lim_ge0`
  + `adde_def_nneg_series` -> `adde_def_nneseries`
- in `esum.v`:
  + `ereal_pseries_esum` -> `nneseries_esum`
- in `numfun.v`:
  + `funenng` -> `funepos`
  + `funennp` -> `funeneg`
  + `funenng_ge0` -> `funepos_ge0`
  + `funennp_ge0` -> `funeneg_ge0`
  + `funenngN` -> `funeposN`
  + `funennpN` -> `funenegN`
  + `funenng_restrict` -> `funepos_restrict`
  + `funennp_restrict` -> `funeneg_restrict`
  + `ge0_funenngE` -> `ge0_funeposE`
  + `ge0_funennpE` -> `ge0_funenegE`
  + `le0_funenngE` -> `le0_funeposE`
  + `le0_funennpE` -> `le0_funenegE`
  + `gt0_funenngM` -> `gt0_funeposM`
  + `gt0_funennpM` -> `gt0_funenegM`
  + `lt0_funenngM` -> `lt0_funeposM`
  + `lt0_funennpM` -> `lt0_funenegM`
  + `funenngnnp` -> `funeposneg`
  + `add_def_funennpg` -> `add_def_funeposneg`
  + `funeD_Dnng` -> `funeD_Dpos`
  + `funeD_nngD` -> `funeD_posD`
- in `lebesgue_measure.v`:
  + `emeasurable_fun_funenng` -> `emeasurable_fun_funepos`
  + `emeasurable_fun_funennp` -> `emeasurable_fun_funeneg`
- in `lebesgue_integral.v`:
  + `integrable_funenng` -> `integrable_funepos`
  + `integrable_funennp` -> `integrable_funeneg`
  + `integral_funennp_lt_pinfty` -> `integral_funeneg_lt_pinfty`
  + `integral_funenng_lt_pinfty` -> `integral_funepos_lt_pinfty`
  + `ae_eq_funenng_funennp` -> `ae_eq_funeposneg`

### Removed

- in `mathcomp_extra.v`:
  + lemmas `natr_absz`, `ge_pinfty`, `le_ninfty`, `gt_pinfty`,
    `lt_ninfty`
- in `classical_sets.v`:
  + notation `[set of _]`
- in `topology.v`:
  + lemmas `inj_can_sym_in_on`, `inj_can_sym_on`, `inj_can_sym_in`

### Infrastructure

### Misc
