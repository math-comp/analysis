# Changelog (unreleased)

## [Unreleased]

### Added

- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `topology.v`:
  + lemma `globally0`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`
- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
- in `lebesgue_measure.v`:
  + lemma `emeasurable_itv`
- in `lebesgue_integral.v`:
  + lemma `sfinite_Fubini`
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
- in `topoogy.v`
  + definitions `sup_pseudoMetricType`, `product_pseudoMetricType`

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
  + lemma `measurable_fun_bool`
- in `constructive_ereal.v`:
  + lemma `lt0e`
- in `lebesgue_integral.v`:
  + lemma `le_integral_comp_abse`

- file `itv.v`:
  + definition `wider_itv`
  + module `Itv`:
    * definitions `map_itv_bound`, `map_itv`
    * lemmas `le_map_itv_bound`, `subitv_map_itv`
    * definition `itv_cond`
    * record `def`
    * notation `spec`
    * record `typ`
    * definitions `mk`, `from`, `fromP`
  + notations `{itv R & i}`, `{i01 R}`, `%:itv`, `[itv of _]`, `inum`, `%:inum`
  + definitions `itv_eqMixin`, `itv_choiceMixin`, `itv_porderMixin`
  + canonical `itv_subType`, `itv_eqType`, `itv_choiceType`, `itv_porderType`
  + lemma `itv_top_typ_subproof`
  + canonical `itv_top_typ`
  + lemma `typ_inum_subproof`
  + canonical `typ_inum`
  + notation `unify_itv`
  + lemma `itv_intro`
  + definition `empty_itv`
  + lemmas `itv_bottom`, `itv_gt0`, `itv_le0F`, `itv_lt0`, `itv_ge0F`, `itv_ge0`, `lt0F`, `le0`, `gt0F`, `lt1`,
    `ge1F`, `le1`, `gt1F`
  + lemma `widen_itv_subproof`
  + definition `widen_itv`
  + lemma `widen_itvE`
  + notation `%:i01`
  + lemma `zero_inum_subproof`
  + canonical `zero_inum`
  + lemma `one_inum_subproof`
  + canonical `one_inum`
  + definition `opp_itv_bound_subdef`
  + lemmas `opp_itv_ge0_subproof`, `opp_itv_gt0_subproof`, `opp_itv_boundr_subproof`,
    `opp_itv_le0_subproof`, `opp_itv_lt0_subproof`, `opp_itv_boundl_subproof`
  + definition `opp_itv_subdef`
  + lemma `opp_inum_subproof `
  + canonical `opp_inum`
  + definitions `add_itv_boundl_subdef`, `add_itv_boundr_subdef`, `add_itv_subdef`
  + lemma `add_inum_subproof`
  + canonical `add_inum`
  + definitions `itv_bound_signl`, `itv_bound_signr`, `interval_sign`
  + variant `interval_sign_spec`
  + lemma `interval_signP`
  + definitions `mul_itv_boundl_subdef`, `mul_itv_boundr_subdef`
  + lemmas `mul_itv_boundl_subproof`, `mul_itv_boundrC_subproof`, `mul_itv_boundr_subproof`,
    `mul_itv_boundr'_subproof`
  + definition `mul_itv_subdef`
  + lemmas `map_itv_bound_min`, `map_itv_bound_max`, `mul_inum_subproof`
  + canonical `mul_inum`
  + lemmas `inum_eq`, `inum_le`, `inum_lt`

- file `itv.v`:
  + definition `wider_itv`
  + module `Itv`:
    * definitions `map_itv_bound`, `map_itv`
    * lemmas `le_map_itv_bound`, `subitv_map_itv`
    * definition `itv_cond`
    * record `def`
    * notation `spec`
    * record `typ`
    * definitions `mk`, `from`, `fromP`
  + notations `{itv R & i}`, `{i01 R}`, `%:itv`, `[itv of _]`, `inum`, `%:inum`
  + definitions `itv_eqMixin`, `itv_choiceMixin`, `itv_porderMixin`
  + canonical `itv_subType`, `itv_eqType`, `itv_choiceType`, `itv_porderType`
  + lemma `itv_top_typ_subproof`
  + canonical `itv_top_typ`
  + lemma `typ_inum_subproof`
  + canonical `typ_inum`
  + notation `unify_itv`
  + lemma `itv_intro`
  + definition `empty_itv`
  + lemmas `itv_bottom`, `itv_gt0`, `itv_le0F`, `itv_lt0`, `itv_ge0F`, `itv_ge0`, `lt0F`, `le0`, `gt0F`, `lt1`,
    `ge1F`, `le1`, `gt1F`
  + lemma `widen_itv_subproof`
  + definition `widen_itv`
  + lemma `widen_itvE`
  + notation `%:i01`
  + lemma `zero_inum_subproof`
  + canonical `zero_inum`
  + lemma `one_inum_subproof`
  + canonical `one_inum`
  + definition `opp_itv_bound_subdef`
  + lemmas `opp_itv_ge0_subproof`, `opp_itv_gt0_subproof`, `opp_itv_boundr_subproof`,
    `opp_itv_le0_subproof`, `opp_itv_lt0_subproof`, `opp_itv_boundl_subproof`
  + definition `opp_itv_subdef`
  + lemma `opp_inum_subproof `
  + canonical `opp_inum`
  + definitions `add_itv_boundl_subdef`, `add_itv_boundr_subdef`, `add_itv_subdef`
  + lemma `add_inum_subproof`
  + canonical `add_inum`
  + definitions `itv_bound_signl`, `itv_bound_signr`, `interval_sign`
  + variant `interval_sign_spec`
  + lemma `interval_signP`
  + definitions `mul_itv_boundl_subdef`, `mul_itv_boundr_subdef`
  + lemmas `mul_itv_boundl_subproof`, `mul_itv_boundrC_subproof`, `mul_itv_boundr_subproof`,
    `mul_itv_boundr'_subproof`
  + definition `mul_itv_subdef`
  + lemmas `map_itv_bound_min`, `map_itv_bound_max`, `mul_inum_subproof`
  + canonical `mul_inum`
  + lemmas `inum_eq`, `inum_le`, `inum_lt`
- in `mathcomp_extra.v`
  + lemma `ler_sqrt`
- in `constructive_ereal.v`
  + definition `sqrte`
  + lemmas `sqrte0`, `sqrte_ge0`, `lee_sqrt`, `sqrteM`, `sqr_sqrte`,
    `sqrte_sqr`, `sqrte_fin_num`
- in `exp.v`:
  + lemma `ln_power_pos`
  + definition `powere_pos`, notation ``` _ `^ _ ``` in `ereal_scope`
  + lemmas `powere_pos_EFin`, `powere_posyr`, `powere_pose0`,
    `powere_pose1`, `powere_posNyr` `powere_pos0r`, `powere_pos1r`,
    `powere_posNyr`, `fine_powere_pos`, `powere_pos_ge0`,
    `powere_pos_gt0`, `powere_pos_eq0`, `powere_posM`, `powere12_sqrt`
- in `measure.v`:
  + lemma `measurable_fun_bigcup`
- in `sequences.v`:
  + lemma `eq_eseriesl`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`

- in `lebesgue_measure.v`:
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`
- in `convex.v`:
  + lemmas `conv_gt0`, `convRE`

- in `exp.v`:
  + lemmas `concave_ln`, `conjugate_powR`

- in file `lebesgue_integral.v`,
  + new lemmas `integral_le_bound`, `continuous_compact_integrable`, and 
    `lebesgue_differentiation_continuous`.

- in `normedtype.v`:
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`

- in `lebesgue_measure.v`:
  + lemma `measurable_ball`

- in file `normedtype.v`,
  + new lemmas `normal_openP`, `uniform_regular`,
    `regular_openP`, and `pseudometric_normal`.
- in file `topology.v`,
  + new definition `regular_space`.
  + new lemma `ent_closure`.

- in file `lebesgue_integral.v`,
  + new lemmas `simple_bounded`, `measurable_bounded_integrable`, 
    `compact_finite_measure`, `approximation_continuous_integrable`

- in `sequences.v`:
  + lemma `cvge_harmonic`

- in `mathcomp_extra.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq`

- in `constructive_ereal.v`:
  + lemma `bigmaxe_fin_num`

### Changed
  
### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
