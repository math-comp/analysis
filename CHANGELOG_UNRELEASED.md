# Changelog (unreleased)

## [Unreleased]

### Added

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
  + lemmas `set_compose_subset`, `compose_diag`
  + notation `\;` for the composition of relations
- OPAM package `coq-mathcomp-classical` containing `boolp.v`
- file `all_classical.v`
- in file `mathcomp_extra.v`:
  + lemmas `pred_oappE` and `pred_oapp_set` (from `classical_sets.v`)
  + lemma `sumr_le0`
- in file `fsbigop.v`:
  + lemmas `fsumr_ge0`, `fsumr_le0`, `fsumr_gt0`, `fsumr_lt0`, `pfsumr_eq0`,
    `pair_fsbig`, `exchange_fsbig`
- in file `ereal.v`:
  + notation `\sum_(_ \in _) _` (from `fsbigop.v`)
  + lemmas `fsume_ge0`, `fsume_le0`, `fsume_gt0`, `fsume_lt0`,
    `pfsume_eq0`, `lee_fsum_nneg_subset`, `lee_fsum`,
    `ge0_mule_fsumr`, `ge0_mule_fsuml` (from `fsbigop.v`)
  + lemmas `finite_supportNe`, `dual_fsumeE`, `dfsume_ge0`, `dfsume_le0`,
    `dfsume_gt0`, `dfsume_lt0`, `pdfsume_eq0`, `le0_mule_dfsumr`, `le0_mule_dfsuml`
- file `classical/set_interval.v`
- in file `classical/set_interval.v`:
  + definitions `neitv`, `set_itv_infty_set0`, `set_itvE`,
    `disjoint_itv`, `conv`, `factor`, `ndconv` (from `set_interval.v`)
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itv_cc`,
    `set_itvco`, `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`,
    `set_itv_infty_infty`, `set_itv_o_infty`, `set_itv_c_infty`, `set_itv_infty_o`,
    `set_itv_infty_c`, `set_itv_pinfty_bnd`, `set_itv_bnd_ninfty`, `setUitv1`,
    `setU1itv`, `set_itvI`, `neitvE`, `neitvP`, `setitv0`, `has_lbound_itv`,
    `has_ubound_itv`, `hasNlbound`, `hasNubound`, `opp_itv_bnd_infty`,
    `opp_itv_infty_bnd`, `opp_itv_bnd_bnd`, `opp_itvoo`,
    `setCitvl`, `setCitvr`, `set_itv_splitI`, `setCitv`, `set_itv_splitD`,
    `mem_1B_itvcc`, `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`,
    `conv1`, `conv_sym`, `conv_flat`, `leW_conv`, `leW_factor`,
    `factor_flat`, `factorl`, `ndconvE`, `factorr`, `factorK`,
    `convK`, `conv_inj`, `factor_inj`, `conv_bij`, `factor_bij`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`, `conv_itv_bij`,
    `factor_itv_bij`, `mem_conv_itv`, `mem_conv_itvcc`, `range_conv`,
    `range_factor`, `mem_factor_itv`,
    `set_itv_ge`, `trivIset_set_itv_nth`, `disjoint_itvxx`, `lt_disjoint`,
    `disjoint_neitv`, `neitv_bnd1`, `neitv_bnd2` (from `set_interval.v`)
  + lemmas `setNK`, `lb_ubN`, `ub_lbN`, `mem_NE`, `nonemptyN`, `opp_set_eq0`,
    `has_lb_ubN`, `has_ubPn`, `has_lbPn` (from `reals.v`)
- in `classical_sets.v`:
  + lemma `bigsetU_sup`
- in `lebesgue_integral.v`:
  + lemmas `emeasurable_fun_fsum`, `ge0_integral_fsum`
- in `ereal.v`:
  + lemma `fsumEFin`
- in `lebesgue_measure.v`:
  + definition `ErealGenInftyO.R` and lemma `ErealGenInftyO.measurableE`
  + lemma `sub1set`
- in `constructive_ereal.v`:
  + lemmas `lteN10`, `leeN10`
  + lemmas `le0_fin_numE`
  + lemmas `fine_lt0`, `fine_le0`
- in `sequences.v`:
  + lemmas `is_cvg_ereal_npos_natsum_cond`, `lee_npeseries`,
    `is_cvg_npeseries_cond`, `is_cvg_npeseries`, `npeseries_le0`,
    `is_cvg_ereal_npos_natsum`
  + lemma `nnseries_is_cvg`
- in `constructive_ereal.v`:
  + lemma `fine_lt0E`
- in file `normedtype.v`
  + lemmas `closed_ballR_compact` and `locally_compactR`

- in `sequences.v`:
  + lemma `invr_cvg0` and `invr_cvg_pinfty`
  + lemma `cvgPninfty_lt`, `cvgPpinfty_near`, `cvgPninfty_near`,
    `cvgPpinfty_lt_near` and `cvgPninfty_lt_near`
- in `classical_sets.v`:
  + notations `\bigcup_(i < n) F` and `\bigcap_(i < n) F`
- in `classical_sets.v`:
  + lemma `preimage_range`
- in `topology.v`
  + definition `separates_points_from_closed`, `join_product`
  + lemma `hausdorff_accessible`
  + lemmas `weak_sep_cvg`, `weak_sep_nbhsE`, `weak_sep_openE`,
      `join_product_continuous`, `join_product_open`, `join_product_inj`,
      `join_product_weak`

- in `fsbig.v`:
  + lemma `fsbig_setU_set1`
- in `tooplogy.v`:
  + lemmas `closed_bigsetU`, `accessible_finite_set_closed`


- in file `classical_sets.v`,
  + new lemma `preimage_range`.
- in file `topology.v`,
  + new lemmas `eq_cvg`, `eq_is_cvg`, `eq_near`, `cvg_toP`, `cvgNpoint`,
    `filter_imply`, `nbhs_filter`, `near_fun`, `cvgnyPgt`, `cvgnyPgty`,
    `cvgnyPgey`, `fcvg_ballP`, `fcvg_ball`, and `fcvg_ball2P`.
- in `topology.v`, added `near do` and `near=> x do` tactic notations
  to perform some tactics under a `\forall x \near F, ...` quantification.
- in `normedtype.v`, added notations `^'+`, `^'-`, `+oo_R`, `-oo_R`

- in file `topology.v`,
  + new definitions `quotient_topology`, and `quotient_open`.
  + new lemmas `pi_continuous`, `quotient_continuous`, and
    `repr_comp_continuous`.

  + new definitions `hausdorff_accessible`, `separates_points_from_closed`, and 
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
