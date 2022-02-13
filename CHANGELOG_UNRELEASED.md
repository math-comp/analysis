# Changelog (unreleased)

  in `trigo.v`, the `realType` argument of `pi` is implicit
  in `trigo.v`, the printed type of `acos`, `asin`, `atan` is `R -> R`

## [Unreleased]

### Added

- in `reals.v`:
  + lemmas `sup_gt`, `inf_lt`, `ltr_add_invr`
- in `normedtype.v`:
  + lemmas `abse_continuous`, `cvg_abse`, `is_cvg_abse`
- in `sequences.v`:
  + definition `eseries` with notation `[eseries E]_n`
    + lemmas `eseriesEnat`, `eseriesEord`, `eseriesSr`, `eseriesS`,
      `eseriesSB`, `eseries_addn`, `sub_eseries_geq`, `sub_eseries`,
      `sub_double_eseries`, `eseriesD`
  + definition `etelescope`
  + lemma `ereal_cvgB`
  + lemmas `lim_mkord`, `ereal_pseries_mkcond`
- in `topology.v`:
  + lemmas `connected1`, `connectedU`
  + lemmas `connected_component_sub`, `connected_component_id`,
    `connected_component_out`, `connected_component_max`, `connected_component_refl`,
    `connected_component_cover`, `connected_component_cover`, `connected_component_trans`,
    `same_connected_component`
- in `ereal.v`:
  + notation `\-`
  + lemmas `fin_numEn`, `fin_numPn`, `oppe_eq0`, `ltpinfty_adde_def`,
    `gte_opp`, `gte_dopp`, `gt0_mulpinfty`, `lt0_mulpinfty`, `gt0_mulninfty`, `lt0_mulninfty`,
    `eq_infty`, `eq_ninfty`, `hasNub_ereal_sup`, `ereal_sup_EFin`, `ereal_inf_EFin`,
    `restrict_abse`
  + canonical `ereal_pointed`
- in `boolp.v`:
  + lemmas `cid2`, `propeqP`, `funeqP`, `funeq2P`, `funeq3P`, `predeq2P`,
    `predeq3P`
  + hint `Prop_irrelevance`
  + lemmas `pselectT`, `eq_opE`
  + definition `classicType`, canonicals `classicType_eqType`,
    `classicType_choiceType`, notation `{classic ...}`
  + definition `eclassicType`, canonicals `eclassicType_eqType`,
    `eclassicType_choiceType`, notation `{eclassic ...}`
  + definition `canonical_of`, notations `canonical_`, `canonical`, lemma `canon`
  + lemmas `Peq`, `Pchoice`, `eqPchoice`
  + lemmas `contra_notT`, `contraPT`, `contraTP`, `contraNP`,
    `contraNP`, `contra_neqP`, `contra_eqP`
  + lemmas `forallPNP`, `existsPNP`
- in `csum.v`:
  + lemmas `sum_fset_set`, `csum_ge`, `csum0`, `le_csum`, `eq_csum`, `csumD`,
    `csum_mkcond`, `csum_mkcondr`, `csum_mkcondl`, `csumID`, `csum_sum`,
    `csum_csum`, `lee_sum_fset_nat`, `lee_sum_fset_lim`, `reindex_csum`,
    `csum_pred_image`, `csum_set_image`, `csum_bigcupT`
- in `classical_sets.v`:
  + notations `[set: ...]`, `` `*`` ``, `` ``*` ``
  + definitions `setMR` and `setML`, `disj_set`
  + coercion `set_type`, definition `SigSub`
  + lemmas `set0fun`, `set_mem`, `mem_setT`, `mem_setK`, `set_memK`,
    `memNset`, `setTPn`, `in_set0`, `in_setT`, `in_setC`, `in_setI`,
    `in_setD`, `in_setU`, `in_setM`, `set_valP`, `set_true`, `set_false`, `set_andb`,
    `set_orb`, `fun_true`, `fun_false`, `set_mem_set`, `mem_setE`,
    `setDUK`, `setDUK`, `setDKU`, `setUv`, `setIv`, `setvU`, `setvI`, `setUCK`,
    `setUKC`, `setICK`, `setIKC`, `setDIK`, `setDKI`, `setI1`, `set1I`,
    `subsetT`, `disj_set2E`, `disj_set2P`, `disj_setPS`, `disj_set_sym`,
    `disj_setPCl`, `disj_setPCr`, `disj_setPLR`, `disj_setPRL`, `setF_eq0`,
    `subsetCl`, `subsetCr`, `subsetC2`, `subsetCP`, `subsetCPl`, `subsetCPr`,
    `subsetUl`, `subsetUr`, `setDidl`, `subIsetl`, `subIsetr`, `subDsetl`, `subDsetr`
    `setUKD`, `setUDK`, `setUIDK`, `bigcupM1l`, `bigcupM1r`, `pred_omapE`, `pred_omap_set`
  + hints `subsetUl`, `subsetUr`, `subIsetl`, `subIsetr`, `subDsetl`, `subDsetr`
  + lemmas `image2E`
  + lemmas `Iiota`, `ordII`, `IIord`, `ordIIK`, `IIordK`
  + lemmas `set_imfset`, `imageT`
  + hints `imageP`, `imageT`
  + lemmas `homo_setP`, `image_subP`, `image_sub`, `subset_set2`
  + lemmas `eq_preimage`, `comp_preimage`, `preimage_id`, `preimage_comp`,
    `preimage_setI_eq0`, `preimage0eq`, `preimage0`, `preimage10`,
  + lemmas `some_set0`, `some_set1`, `some_setC`, `some_setR`, `some_setI`, `some_setU`,
    `some_setD`, `sub_image_some`, `sub_image_someP`, `image_some_inj`, `some_set_eq0`,
    `some_preimage`, `some_image`, `disj_set_some`
  + lemmas `some_bigcup`, `some_bigcap`, `bigcup_set_type`, `bigcup_mkcond`,
    `bigcup_mkcondr`, `bigcup_mkcondl`, `bigcap_mkcondr`, `bigcap_mkcondl`,
    `bigcupDr`, `setD_bigcupl`, `bigcup_bigcup_dep`, `bigcup_bigcup`, `bigcupID`.
    `bigcapID`
  + lemmas `bigcup2inE`, `bigcap2`, `bigcap2E`, `bigcap2inE`
  + lemmas `bigcup_sub`, `sub_bigcap`, `bigcap_set_type`, `bigcup_pred`
  + lemmas `bigsetU_bigcup2`, `bigsetI_bigcap2`
  + lemmas `in1TT`, `in2TT`, `in3TT`, `inTT_bij`
  + canonical `option_pointedType`
  + notations `[get x | E]`, `[get x : T | E]`
  + variant `squashed`, notation `$| ... |`, tactic notation `squash`
  + definition `unsquash`, lemma `unsquashK`
  + module `Empty` that declares the type `emptyType` with the expected `[emptyType of ...]` notations
  + canonicals `False_emptyType` and `void_emptyType`
  + definitions `no` and `any`
  + lemmas `empty_eq0`
  + definition `quasi_canonical_of`, notations `quasi_canonical_`, `quasi_canonical`, lemma `qcanon`
  + lemmas `choicePpointed`, `eqPpointed`, `Ppointed`
  + lemmas `trivIset_setIl`, `trivIset_setIr`, `sub_trivIset`, `trivIset_bigcup2`
- in `cardinality.v`:
  + notations `#>=`, `#=`, `#!=`
  + scope `card_scope`, delimiter `card`
  + notation `infinite_set`
  + lemmas `injPex`, `surjPex`, `bijPex`, `surjfunPex`, `injfunPex`
  + lemmas `inj_card_le`, `pcard_leP`, `pcard_leTP`, `pcard_injP`, `ppcard_leP`
  + lemmas `pcard_eq`, `pcard_eqP`, `card_bijP`, `card_eqVP`, `card_set_bijP`
  + lemmas `ppcard_eqP`, `card_eqxx`, `inj_card_eq`, `card_some`, `card_image`,
    `card_imsub`
  + hint `card_eq00`
  + lemmas `empty_eq0`, `card_le_emptyl`, `card_le_emptyr`
  + multi-rule `emptyE_subdef`
  + lemmas `card_eq_le`, `card_eqPle`, `card_leT`, `card_image_le`
  + lemmas `card_le_eql`, `card_le_eqr`, `card_eql`, `card_eqr`,
    `card_ge_image`, `card_le_image`, `card_le_image2`, `card_eq_image`, `card_eq_imager`,
    `card_eq_image2`
  + lemmas `card_ge_some`, `card_le_some`, `card_le_some2`, `card_eq_somel`, `card_eq_somer`,
    `card_eq_some2`
  + lemmas `card_eq_emptyr`, `card_eq_emptyl`, `emptyE`
  + lemma and hint `card_setT`
  + lemma and hint `card_setT_sym`
  + lemmas `surj_card_ge`, `pcard_surjP`, `pcard_geP`, `ocard_geP`, `pfcard_geP`
  + lemmas `ocard_eqP`, `oocard_eqP`, `sub_setP`, `card_subP`
  + lemmas `eq_countable`, `countable_set_countMixin`, `countableP`, `sub_countable`
  + lemmas `card_II`, `finite_fsetP`, `finite_subfsetP`, `finite_seqP`, `finite_fset`, `finite_finpred`,
    `finite_finset`, `infiniteP`, `finite_setPn`
  + lemmas `card_le_finite`, `finite_set_leP`, `card_ge_preimage`, `eq_finite_set`,
    `finite_image`
  + lemma and hint `finite_set1`
  + lemmas `finite_setU`, `finite_set{2,3,4,5,6,7}`, `finite_setI`, `finite_setIl`, `finite_setIr`,
    `finite_setM`, `finite_image2`, `finite_image11`
  + definition `fset_set`
  + lemmas `fset_setK`, `in_fset_set`, `fset_set0`, `fset_set1`, `fset_setU`,
    `fset_setI`, `fset_setU1`, `fset_setD`, `fset_setD1`, `fset_setM`
  + definitions `fst_fset`, `snd_fset`, notations ``` .`1 ```, ``` .`2 ```
  + lemmas `finite_set_fst`, `finite_set_snd`, `bigcup_finite`, `finite_setMR`, `finite_setML`,
    `fset_set_II`, `set_fsetK`, `fset_set_inj`, `bigsetU_fset_set`, `bigcup_fset_set`,
    `bigsetU_fset_set_cond`, `bigcup_fset_set_cond`, `bigsetI_fset_set`, `bigcap_fset_set`,
    `super_bij`, `card_eq_fsetP`, `card_IID`, `finite_set_bij`
  + lemmas `countable1`, `countable_fset`
  + lemma and hint `countable_finpred`
  + lemmas `eq_card_nat`
  + canonical `rat_pointedType`
  + lemmas `infinite_rat`, `card_rat`, `choicePcountable`, `eqPcountable`, `Pcountable`,
    `bigcup_countable`, `countableMR`, `countableM`, `countableML`, `infiniteMRl`, `cardMR_eq_nat`
- in `measure.v`:
  + definitions `set{C,I,U,D,DI}_closed`, `fin_bigcap_closed`, `finN0_bigcap_closed`,
    `fin_bigcup_closed`, `semi_setD_closed`, `ndseq_closed`, `trivIset_closed`, `fin_trivIset_closed`,
    `set_ring`, `sigma_algebra`, `dynkin`, `monotone_classes`, `smallest`
  + notations `<<m D, G >>`, `<<m G >>`, `<<s D, G>>`, `<<s G>>`, `<<d G>>`, `<<r G>>`, `<<fu G>>`
  + lemmas `sub_smallest`, `smallest_sub`, `smallest_id`
  + lemma and hint `sub_gen_smallest`
  + lemmas `sub_smallest2r`, `sub_smallest2l`, `fin_bigcup_closedP`, `finN0_bigcap_closedP`,
    `sedDI_closedP`, `sigma_algebra_bigcap`, `sigma_algebraP`
  + lemma and hint `smallest_sigma_algebra`
  + lemmas `sub_sigma_algebra2`, `sigma_algebra_id`, `sub_sigma_algebra`, `sigma_algebra0`,
    `sigma_algebraD`, `sigma_algebra_bigcup`
  + lemma and hint `smallest_setring`, lemma and hint `setring0`
  + lemmas `sub_setring2`, `setring_id`, `sub_setring`, `setringDI`, `setringU`,
    `setring_fin_bigcup`, `monotone_class_g_salgebra`
  + lemmas `smallest_monotone_classE`, `monotone_class_subset`, `dynkin{T,C,U}`, `dynkin_monotone`,
    `dynkin_g_dynkin`, `sigma_algebra_dynkin`, `dynkin_setI_bigsetI`, `dynkin_setI_sigma_algebra`,
    `setI_closed_gdynkin_salgebra`
  + factories `isRingOfSets`, `isAlgebraOfSets`
  + lemmas `fin_bigcup_measurable`, `fin_bigcap_measurable`, `sigma_algebra_measurable`,
    `sigma_algebraC`
  + definition `g_measurableType`
  + lemmas `measurable_g_measurableTypeE`
  + definitions `preimage_class` and `image_class`
  + lemmas `preimage_class_measurable_fun`, `sigma_algebra_preimage_class`, `sigma_algebra_image_class`,
    `transfer`, `measurability`
  + definition `sub_additive`
  + lemma `semi_additiveW`
  + notation `... \_ ...`
  + lemmas `content_fin_bigcup`, `measure_fin_bigcup`, `measure_bigsetU_ord_cond`, `measure_bigsetU_ord`,
  + coercion `measure_to_nadditive_measure`
  + lemmas `measure_semi_bigcup`, `measure_bigcup`
  + hint `measure_ge0`
  + lemma `big_trivIset`
  + defintion `covered_by`
  + module `SetRing`
    * lemmas `ring_measurableE`, `ring_fsets`
    * definition `decomp`
    * lemmas `decomp_triv`, `decomp_triv`, `decomp_neq0`, `decomp_neq0`, `decomp_measurable`, `cover_decomp`,
      `decomp_sub`, `decomp_set0`, `decomp_set0`
    * definition `measure`
    * lemma `Rmu_fin_bigcup`, `RmuE`, `Rmu0`, `Rmu_ge0`, `Rmu_additive`, `Rmu_additive_measure`
    * canonical `measure_additive_measure`
  + lemmas `covered_byP`, `covered_by_finite`, `covered_by_countable`, `ereal_pseries_sum`,
    `all_sig2_cond`, `bigcap_bigcup`, `measure_le0`, `content_sub_additive`, `content_sub_fsum`,
    `content_ring_sup_sigma_additive`, `content_ring_sigma_additive`, `ring_sigma_sub_additive`,
    `ring_sigma_additive`, `measure_sigma_sub_additive`, `measureIl`, `measureIr`,
    `subset_measure0`, `measureUfinr`, `measureUfinl`, `eq_measureU`, `null_set_setU`
  + lemmas `g_salgebra_measure_unique_trace`, `g_salgebra_measure_unique_cover`, `g_salgebra_measure_unique`,
    `measure_unique`, `measurable_mu_extE`, `Rmu_ext`, `measurable_Rmu_extE`,
    `sub_caratheodory`
  + definition `Hahn_ext`, canonical `Hahn_ext_measure`, lemma `Hahn_ext_sigma_finite`, `Hahn_ext_unique`,
    `caratheodory_measurable_mu_ext`
- new file `mathcomp_extra.v`
- new file `fsbigop.v`
- new file `set_interval.v`
- new file `lebesgue_measure.v`
- new file `lebesgue_integral.v`
- new file `functions`

### Changed

- in `sequences.v`:
  + `\sum` notations for extended real numbers now in `ereal_scope`
  + lemma `ereal_cvg_sub0` is now an equivalence
- in `topology.v`:
  + definition `connected_component`
- in `boolp.v`:
  + `equality_mixin_of_Type`, `choice_of_Type` -> see `classicalType`
- in `csum.v`:
  + lemma `csum_ge0` has now a weaker hypothesis
- notation ``` `I_ ``` moved from `cardinality.v` to `classical_sets.v`
- moved from `classical_types.v` to `boolp.v`:
  + definitions `gen_eq` and `gen_eqMixin`, lemma `gen_eqP`
  + canonicals `arrow_eqType`, `arrow_choiceType`
  + definitions `dep_arrow_eqType`, `dep_arrow_choiceClass`, `dep_arrow_choiceType`
  + canonicals `Prop_eqType`, `Prop_choiceType`
- in `classical_sets.v`:
  + arguments of `preimage`
- in `cardinality.v`:
  + definition `card_eq` now uses `{bij ... >-> ...}`
  + definition `card_le` now uses `{injfun ... >-> ...}`
  + definition `set_finite` changed to `finite_set`
  + definition `card_leP` now uses `reflect`
  + definition `card_le0P` now uses `reflect`
  + definition `card_eqP` now uses `reflect`
  + statement of theorem `Cantor_Bernstein`
  + lemma `subset_card_le` does not require finiteness of rhs anymore
  + lemma `surjective_card_le` does not require finiteness of rhs anymore and renamed to `surj_card_ge`
  + lemma `card_le_diff` does not require finiteness of rhs anymore and renamed to `card_le_setD`
  + lemma `card_eq_sym` now an equality
  + lemma `card_eq0` now an equality
  + lemmas `card_le_II` and `card_eq_II` now equalities
  + lemma `countable_injective` renamed to `countable_injP` and use `reflect`
  + lemmas `II0`, `II1`, `IIn_eq0` moved to `classical_sets.v`
  + lemma `II_recr` renamed to `IIS` and moved to `classical_sets.v`
  + definition `surjective` moved to `functions.v` and renamed `set_sur`
  + definition `set_bijective` moved to `functions.v` and changed to `set_bij`
  + lemma `surjective_id` moved to `functions.v` and renamed `surj_id`
  + lemma `surjective_set0` moved to `functions.v` and renamed `surj_set0`
  + lemma `surjectiveE` moved to `functions.v` and renamed `surjE`
  + lemma `surj_image_eq` moved to `functions.v`
  + lemma `can_surjective` moved to `functions.v` and changed to `can_surj`
  + lemma `surjective_comp` moved to `functions.v` and renamed `surj_comp`
  + lemma `set_bijective1` moved to `functions.v` and renamed `eq_set_bijRL`
  + lemma `set_bijective_image` moved to `functions.v` and renamed `inj_bij`
  + lemma `set_bijective_subset` moved to `functions.v` and changed to `bij_subr`
  + lemma `set_bijective_comp` moved to `functions.v` and renamed `set_bij_comp`
  + definition `inverse` changed to the type `{inv ... >-> ...}`, see `functions.v`
- from `cardinality.v` to `classical_sets.v`:
  + `eq_set0_nil` -> `set_seq_eq0`
  + `eq_set0_fset0` -> `set_fset_eq0`
- in `measure.v`:
  + definition `uncurry` moved to `mathcomp_extra.v`
  + definition `bigcup2`, lemma `bigcup2E`  moved to `mathcomp_extra.v`
  + mixin `isSemiRingOfSets` and `isRingOfSets` changed
  + types `semiRingOfSetsType`, `ringOfSetsType`, `algebraOfSetsType`, `measurableType` now pointed types
  + definition `measurable_fun` changed
  + definition `sigma_sub_additive` changed and renamed to `sigma_subadditive`
  + record `AdditiveMeasure.axioms`
  + lemmas `measure_ge0`
  + record `Measure.axioms`
  + definitions `seqDU`, `seqD`, lemma and hint `trivIset_seqDU`, lemmas `bigsetU_seqDU`, `seqDU_bigcup_eq`,
    `seqDUE`, `trivIset_seqD`, `bigsetU_seqD`, `setU_seqD`, `eq_bigsetU_seqD`, `eq_bigcup_seqD`, `eq_bigcup_seqD_bigsetU`
    moved to `sequences.v`
  + definition `negligibleP` weakened to additive measures
  + lemma `measure_negligible`
  + definition `caratheodory_measurable` and `caratheodory_type` weakened from outer measures to functions
  + lemma `caratheodory_measure_ge0` does take a condition anymore
  + definitions `measurable_cover` and `mu_ext`, canonical `outer_measure_of_measure` weakened to `semiRingOfSetsType`

### Renamed

- in `topology.v`:
  + `cvg_restrict_dep` -> `cvg_sigL`
- in `csum.v`:
  + `csum0` -> `csum_set0`
- in `classical_sets.v`:
  + `mkset_nil` -> `set_nil`
- in `cardinality.v`:
  + `card_le0x` -> `card_ge0`
  + `card_eq_sym` -> `card_esym`
  + `set_finiteP` -> `finite_setP`
  + `set_finite0` -> `finite_set0`
  + `set_finite_seq` -> `finite_seq`
  + `set_finite_countable` -> `finite_set_countable`
  + `subset_set_finite` -> `sub_finite_set`
  + `set_finite_preimage` -> `finite_preimage`
  + `set_finite_diff` -> `finite_setD`
  + `countably_infinite_prod_nat` -> `card_nat2`

### Removed

- in `ereal.v`:
  + lemmas `big_nat_widenl`, `big_geq_mkord`
- in `csum.v`:
  + lemmas `fsets_img`, `fsets_ord`, `fsets_ord_nat`, `fsets_ord_subset`, `csum_bigcup_le`,
    `le_csum_bigcup`
- in `classical_sets.v`:
  + lemma `subsetU`
  + definition `patch`, notations `restrict` and `... \|_ ...`
  + definition `restrict_dep`, `extend_up`, lemma `restrict_depE`
- in `cardinality.v`:
  + lemma `in_inj_comp`
  + lemmas `enum0`, `enum_recr`
  + lemma `image_nat_maximum`, `fset_nat_maximum`
  + lemma `surjective_image`, `surjective_image_eq0`
  + lemmas `inj_of_bij`, `sub_of_bij`, `sur_of_bij`
  + lemmas `injective_left_inverse`, `injective_right_inverse`, `surjective_right_inverse`,
    `set_bijective_D1`
  + lemmas `card_le_surj`, `card_eq00`
  + lemmas `card_eqTT`, `card_eq_II`, `card_eq_le`, `card_leP`
  + lemmas `set_bijective_inverse`, `countable_trans`, `set_bijective_U1`,
    `set_bijective_cyclic_shift`, `set_bijective_cyclic_shift_simple`, `set_finite_bijective`,
    `subset_set_finite_card_le`, `injective_set_finite_card_le`, `injective_set_finite`,
    `injective_card_le`, `surjective_set_finite_card_le`, `set_finite_inter_set0_union`,
    `ex_in_D`.
  + definitions `min_of_D`, `min_of_D_seq`, `infsub_enum`
  + lemmas `min_of_D_seqE`, `increasing_infsub_enum`, `sorted_infsub_enum`, `injective_infsub_enum`,
    `subset_infsub_enum`, `infinite_nat_subset_countable`
  + definition `enumeration`
  + lemmas `enumeration_id`, `enumeration_set0`, `ex_enum_notin`
  + defnitions `min_of_e`, `min_of_e_seq`, `smallest_of_e`, `enum_wo_rep`
  + lemmas `enum_wo_repE`, `min_of_e_seqE`,
    `smallest_of_e_notin_enum_wo_rep`, `injective_enum_wo_rep`, `surjective_enum_wo_rep`,
    `set_bijective_enum_wo_rep`, `enumeration_enum_wo_rep`, `countable_enumeration`
  + definition `nat_of_pair`
  + lemmas `nat_of_pair_inj`, `countable_prod_nat`
- in `measure.v`:
  + definition `diff_fsets`
  + lemmas `semiRingOfSets_measurableI`, `semiRingOfSets_measurableD`, `semiRingOfSets_diff_fsetsE`,
    `semiRingOfSets_diff_fsets_disjoint`

### Infrastructure

### Misc
