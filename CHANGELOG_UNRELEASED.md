# Changelog (unreleased)

## [Unreleased]

### Added
- in `normedtype.v`:
  + lemmas `not_near_inftyP`, `not_near_ninftyP`

- in `topology.v`:
  + lemma `filterN`

- in `normedtype.v`:
  + lemma `ninftyN`

- in `derive.v`:
  + lemma `derive_id`
  + lemmas `exp_derive`, `exp_derive1`
  + lemma `derive_cst`
  + lemma `deriveMr`, `deriveMl`

- in `functions.v`:
  + lemmas `mul_funC`
- in `sequences.v`:
  + lemma `cvg_geometric_eseries_half`

- in `lebesgue_measure.v`:
  + definitions `is_open_itv`, `open_itv_cover`
  + lemmas `outer_measure_open_itv_cover`, `outer_measure_open_le`,
    `outer_measure_open`, `outer_measure_Gdelta`, `negligible_outer_measure`

- in `classical_sets.v`:
  + scope `relation_scope` with delimiter `relation`
  + notation `^-1` in `relation_scope` (use to be a local notation)
  + lemma `set_prod_invK` (was a local lemma in `normedtype.v`)
  + definition `diagonal`, lemma `diagonalP`
- in `mathcomp_extra.v`:
  + lemmas `invf_ple`, `invf_lep`

- in `lebesgue_integral.v`:
  + lemma `integralZr`
  + lemma `nneseries_recl`

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
  
- in `topology.v`:
  + global instance `ball_filter`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pointedType`, `filteredType`, `topologicalType`,
      `uniformType`, `pseudoMetricType`
  + module `numFieldTopology` with an `Exports` submodule
    * many canonicals and coercions
  + global instance `Proper_nbhs'_regular_numFieldType`
- in `normedtype.v`:
  + definitions `ball_`, `pointed_of_zmodule`, `filtered_of_normedZmod`
  + lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`
  + definition `pseudoMetric_of_normedDomain`
  + lemma `nbhs_ball_normE`
  + global instances `Proper_nbhs'_numFieldType`, `Proper_nbhs'_realType`
  + module `regular_topology` with an `Exports` submodule
    * canonicals `pseudoMetricNormedZmodType`, `normedModType`.
  + module `numFieldNormedType` with an `Exports` submodule
    * many canonicals and coercions
    * exports `Export numFieldTopology.Exports`
  + canonical `R_regular_completeType`, `R_regular_CompleteNormedModule`
- in `reals.v`:
  + lemmas `Rfloor_lt0`, `floor_lt0`, `ler_floor`, `ceil_gt0`, `ler_ceil`
- in `ereal.v`:
  + lemmas `ereal_ballN`, `le_ereal_ball`, `ereal_ball_ninfty_oversize`,
    `contract_ereal_ball_pinfty`, `expand_ereal_ball_pinfty`,
    `contract_ereal_ball_fin_le`, `contract_ereal_ball_fin_lt`,
    `expand_ereal_ball_fin_lt`, `ball_ereal_ball_fin_lt`, `ball_ereal_ball_fin_le`,
    `sumERFin`, `ereal_inf1`, `eqe_oppP`, `eqe_oppLRP`, `oppe_subset`,
    `ereal_inf_pinfty`
  + definition `er_map`
  + definition `er_map`
- in `classical_sets.v`:
  + notation `[disjoint ... & ..]`
  + lemmas `mkset_nil`, `bigcup_mkset`, `bigcup_nonempty`, `bigcup0`, `bigcup0P`,
    `subset_bigcup_r`, `eqbigcup_r`, `eq_set_inl`, `set_in_in`
- in `ereal.v`:
  + lemmas `adde_undefC`, `real_of_erD`, `fin_num_add_undef`, `addeK`,
    `subeK`, `subee`, `sube_le0`, `lee_sub`
  + lemmas `addeACA`, `muleC`, `mule1`, `mul1e`, `abseN`
  + enable notation `x \is a fin_num`
    * definition `fin_num`, fact `fin_num_key`, lemmas `fin_numE`, `fin_numP`
  + definition `dense` and lemma `denseNE`
- in `reals.v`:
  + lemmas `has_sup1`, `has_inf1`
- in `nngnum.v`:
  + instance `invr_nngnum`
- in `posnum.v`:
  + instance `posnum_nngnum`

- file `banach_steinhaus.v`:
  + definition `dense`
  + lemma `denseNE`
  + lemma `le_closed_ball`
  + lemma `floor_nat_comp`
  + definition `Baire`
  + theorem `DeBaire`
  + definition `bounded_fun_norm`
  + lemma `bounded_landau`
  + definition `pointwise_bounded`
  + definition `uniform_bounded`
  + theorem `Banach_Steinhauss`

### Changed

- in `normedtype.v`:
  + remove superflous parameters in lemmas `not_near_at_rightP` and `not_near_at_leftP`

### Renamed

- in `lebesgue_measure.v`:
  + `measurable_exprn` -> `exprn_measurable`
  + `measurable_mulrl` -> `mulrl_measurable`
  + `measurable_mulrr` -> `mulrr_measurable`
  + `measurable_fun_pow` -> `measurable_funX`
  + `measurable_oppe` -> `oppe_measurable`
  + `measurable_abse` -> `abse_measurable`
  + `measurable_EFin` -> `EFin_measurable`
  + `measurable_oppr` -> `oppr_measurable`
  + `measurable_normr` -> `normr_measurable`
  + `measurable_fine` -> `fine_measurable`
  + `measurable_natmul` -> `natmul_measurable`
- in `topology.v`:
  + in mixin `Nbhs_isUniform_mixin`:
    * `entourage_refl_subproof` -> `entourage_diagonal_subproof`
  + in factory `Nbhs_isUniform`:
    * `entourage_refl` -> `entourage_diagonal`
  + in factory `isUniform`:
    * `entourage_refl` -> `entourage_diagonal`

### Generalized

- in `derive.v`:
  + lemma `derivable_cst`

- in `lebesgue_measure.v`:
  + lemma `measurable_funX` (was `measurable_fun_pow`)

- in `lebesgue_integral.v`
  + lemma `ge0_integral_closed_ball`

### Deprecated

### Removed

- in `lebesgue_measure.v`:
  + notation `measurable_fun_sqr` (was deprecated since 0.6.3)
  + notation `measurable_fun_exprn` (was deprecated since 0.6.3)
  + notation `measurable_funrM` (was deprecated since 0.6.3)
  + notation `emeasurable_fun_minus` (was deprecated since 0.6.3)
  + notation `measurable_fun_abse` (was deprecated since 0.6.3)
  + notation `measurable_fun_EFin` (was deprecated since 0.6.3)
  + notation `measurable_funN` (was deprecated since 0.6.3)
  + notation `measurable_fun_opp` (was deprecated since 0.6.3)
  + notation `measurable_fun_normr` (was deprecated since 0.6.3)
  + notation `measurable_fun_fine` (was deprecated since 0.6.3)
- in `topology.v`:
  + turned into Let's (inside `HB.builders`):
    * lemmas `nbhsE_subproof`, `openE_subproof`
    * lemmas `nbhs_pfilter_subproof`, `nbhsE_subproof`, `openE_subproof`
    * lemmas `open_fromT`, `open_fromI`, `open_from_bigU`
    * lemmas `finI_from_cover`, `finI_from_join`
    * lemmas `nbhs_filter`, `nbhs_singleton`, `nbhs_nbhs`
    * lemmas `ball_le`, `entourage_filter_subproof`, `ball_sym_subproof`,
      `ball_triangle_subproof`, `entourageE_subproof`

### Infrastructure

### Misc
