# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal.v`:
  + lemmas `esum_ninftyP`, `esum_pinftyP`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinftyP`, `desum_ninftyP`
  + lemmas `lee_pemull`, `lee_nemul`, `lee_pemulr`, `lee_nemulr`
- in `sequences.v`:
  + lemmas `ereal_cvgM_gt0_pinfty`, `ereal_cvgM_lt0_pinfty`, `ereal_cvgM_gt0_ninfty`,
    `ereal_cvgM_lt0_ninfty`, `ereal_cvgM`
- in `ereal.v`:
  + lemma `fin_numM`
  + definition `mule_def`, notation `x *? y`
  + lemma `mule_defC`
  + notations `\*` in `ereal_scope`, and `ereal_dual_scope`
- in `ereal.v`:
  + lemmas `mule_def_fin`, `mule_def_neq0_infty`, `mule_def_infty_neq0`, `neq0_mule_def`
  + notation `\-` in `ereal_scope` and `ereal_dual_scope`
  + lemma `fin_numB`
  + lemmas `mule_eq_pinfty`, `mule_eq_ninfty`
  + lemmas `fine_eq0`, `abse_eq0`
- in `topology.v`:
  + lemma `filter_pair_set`
- in `topology.v`:
  + definition `prod_topo_apply`
  + lemmas `prod_topo_applyE`, `prod_topo_apply_continuous`, `hausdorff_product`
- in `topology.v`:
  + lemmas `closedC`, `openC` 
  + lemmas `continuous_subspace_in`
  + lemmas`closed_subspaceP`, `closed_subspaceW`, `closure_subspaceW`
  + lemmas `nbhs_subspace_subset`, `continuous_subspaceW`, `nbhs_subspaceT`,
    `continuous_subspaceT_for`, `continuous_subspaceT`, `continuous_open_subspace`
  + globals `subspace_filter`, `subspace_proper_filter`
  + notation `{within ..., continuous ...}`
- in `derive.v`
  + lemma `MVT_segment`
- in `normedtype.v`
  + generalize `IVT` with subspace topology
- in `realfun.v`:
  + lemma `continuous_subspace_itv`
- in `topology.v`:
  + definitions `compact_near`, `precompact`, `locally_compact`
  + lemmas `precompactE`, `precompact_subset`, `compact_precompact`, 
    `precompact_closed`
  + definitions `singletons`, `equicontinuous`, `pointwise_precompact`
  + lemmas `equicontinuous_subset`, `equicontinuous_cts`
  + lemmas `pointwise_precomact_subset`, `pointwise_precompact_precompact`
    `uniform_pointwise_compact`, `compact_pointwise_precompact`
  + lemmas `compact_set1`, `uniform_set1`, `ptws_cvg_family_singleton`,
    `ptws_cvg_compact_family`
- in `reals.v`:
  + lemmas `sup_gt`, `inf_lt`, `ltr_add_invr`
- in `normedtype.v`:
  + lemmas `abse_continuous`, `cvg_abse`, `is_cvg_abse`, `EFin_lim`, `near_infty_natSinv_expn_lt`
- in `topology.v`:
  + lemmas `connected1`, `connectedU`
  + lemmas `connected_component_sub`, `connected_component_id`,
    `connected_component_out`, `connected_component_max`, `connected_component_refl`,
    `connected_component_cover`, `connected_component_cover`, `connected_component_trans`,
    `same_connected_component`
  + lemma `continuous_is_cvg`
- in `ereal.v`:
  + lemmas `EFin_inj`, `EFin_bigcup`, `EFin_setC`, `adde_gt0`, `mule_ge0_gt0`,
    `lte_mul_pinfty`, `lt0R`, `adde_defEninfty`, `lte_pinfty_eq`, `ge0_fin_numE`, `eq_pinftyP`,
  + canonical `mule_monoid`
  + lemmas `preimage_abse_pinfty`, `preimage_abse_ninfty`
  + notation `\-`
  + lemmas `fin_numEn`, `fin_numPn`, `oppe_eq0`, `ltpinfty_adde_def`,
    `gte_opp`, `gte_dopp`, `gt0_mulpinfty`, `lt0_mulpinfty`, `gt0_mulninfty`, `lt0_mulninfty`,
    `eq_infty`, `eq_ninfty`, `hasNub_ereal_sup`, `ereal_sup_EFin`, `ereal_inf_EFin`,
    `restrict_abse`
  + canonical `ereal_pointed`
  + lemma `seq_psume_eq0`
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
  + module `FunOrder`, lemma `lefP`
- in `sequences.v`:
  + definition `eseries` with notation `[eseries E]_n`
    + lemmas `eseriesEnat`, `eseriesEord`, `eseriesSr`, `eseriesS`,
      `eseriesSB`, `eseries_addn`, `sub_eseries_geq`, `sub_eseries`,
      `sub_double_eseries`, `eseriesD`
  + definition `etelescope`
  + lemmas `ereal_cvgB`, `nondecreasing_seqD`, `lef_at`
  + lemmas `lim_mkord`, `ereal_pseries_mkcond`, `ereal_pseries_sum`
  + definition `sdrop`
  + lemmas `has_lbound_sdrop`, `has_ubound_sdrop`
  + definitions `sups`, `infs`
  + lemmas `supsN`, `infsN`, `nonincreasing_sups`, `nondecreasing_infs`, `is_cvg_sups`, `is_cvg_infs`,
    `infs_le_sups`, `cvg_sups_inf`, `cvg_infs_sup`, `sups_preimage`, `infs_preimage`, `bounded_fun_has_lbound_sups`,
    `bounded_fun_has_ubound_infs`
  + definitions `lim_sup`, `lim_inf`
  + lemmas `lim_infN`, `lim_supE`, `lim_infE`, `lim_inf_le_lim_sup`, `cvg_lim_inf_sup`,
    `cvg_lim_infE`, `cvg_lim_supE`, `cvg_sups`, `cvg_infs`, `le_lim_supD`, `le_lim_infD`,
    `lim_supD`, `lim_infD`
  + definitions `esups`, `einfs`
  + lemmas `esupsN`, `einfsN`, `nonincreasing_esups`, `nondecreasing_einfs`, `einfs_le_esups`,
    `cvg_esups_inf`, `is_cvg_esups`, `cvg_einfs_sup`, `is_cvg_einfs`, `esups_preimage`, `einfs_preimage`
  + definitions `elim_sup`, `elim_inf`
  + lemmas `elim_infN`, `elim_supN`, `elim_inf_sup`, `elim_inf_sup`, `cvg_ninfty_elim_inf_sup`,
    `cvg_ninfty_einfs`, `cvg_ninfty_esups`, `cvg_pinfty_einfs`, `cvg_pinfty_esups`, `cvg_esups`,
    `cvg_einfs`, `cvg_elim_inf_sup`, `is_cvg_elim_infE`, `is_cvg_elim_supE`
  + lemmas `elim_inf_shift`, `elim_sup_le_cvg`
- in `esum.v` (was `csum.v`):
  + lemmas `sum_fset_set`, `esum_ge`, `esum0`, `le_esum`, `eq_esum`, `esumD`,
    `esum_mkcond`, `esum_mkcondr`, `esum_mkcondl`, `esumID`, `esum_sum`,
    `esum_esum`, `lee_sum_fset_nat`, `lee_sum_fset_lim`, `ereal_pseries_esum`, `reindex_esum`,
    `esum_pred_image`, `esum_set_image`, `esum_bigcupT`
- in `classical_sets.v`:
  + notations `[set: ...]`, ``` *` ```, ``` `* ```
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
  + lemmas `bigcup_sub`, `sub_bigcap`, `subset_bigcup`, `subset_bigcap`, `bigcap_set_type`, `bigcup_pred`
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
  + definition `smallest`
  + lemmas `sub_smallest`, `smallest_sub`, `smallest_id`
  + lemma and hint `sub_gen_smallest`
  + lemmas `sub_smallest2r`, `sub_smallest2l`
  + lemmas `preimage_itv`, `preimage_itv_o_infty`, `preimage_itv_c_infty`, `preimage_itv_infty_o`,
    `preimage_itv_infty_c`, `notin_setI_preimage`
  + definitions `xsection`, `ysection`
  + lemmas `xsection0`, `ysection0`, `in_xsectionM`, `in_ysectionM`, `notin_xsectionM`, `notin_ysectionM`,
    `xsection_bigcup`, `ysection_bigcup`, `trivIset_xsection`, `trivIset_ysection`, `le_xsection`,
    `le_ysection`, `xsectionD`, `ysectionD`
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
  + lemmas `finite_setU`, `finite_set2`, `finite_set3`, `finite_set4`, `finite_set5`,
    `finite_set6`, `finite_set7`, `finite_setI`, `finite_setIl`, `finite_setIr`,
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
  + definitions `setC_closed`, `setI_closed`, `setU_closed`, `setD_closed`, `setDI_closed`,
    `fin_bigcap_closed`, `finN0_bigcap_closed`, `fin_bigcup_closed`, `semi_setD_closed`,
    `ndseq_closed`, `trivIset_closed`, `fin_trivIset_closed`, `set_ring`, `sigma_algebra`,
    `dynkin`, `monotone_classes`
  + notations `<<m D, G >>`, `<<m G >>`, `<<s D, G>>`, `<<s G>>`, `<<d G>>`, `<<r G>>`, `<<fu G>>`
  + lemmas `fin_bigcup_closedP`, `finN0_bigcap_closedP`,
    `sedDI_closedP`, `sigma_algebra_bigcap`, `sigma_algebraP`
  + lemma and hint `smallest_sigma_algebra`
  + lemmas `sub_sigma_algebra2`, `sigma_algebra_id`, `sub_sigma_algebra`, `sigma_algebra0`,
    `sigma_algebraD`, `sigma_algebra_bigcup`
  + lemma and hint `smallest_setring`, lemma and hint `setring0`
  + lemmas `sub_setring2`, `setring_id`, `sub_setring`, `setringDI`, `setringU`,
    `setring_fin_bigcup`, `monotone_class_g_salgebra`
  + lemmas `smallest_monotone_classE`, `monotone_class_subset`, `dynkinT`, `dynkinC`, `dynkinU`,
    `dynkin_monotone`, `dynkin_g_dynkin`, `sigma_algebra_dynkin`, `dynkin_setI_bigsetI`,
    `dynkin_setI_sigma_algebra`, `setI_closed_gdynkin_salgebra`
  + factories `isRingOfSets`, `isAlgebraOfSets`
  + lemmas `fin_bigcup_measurable`, `fin_bigcap_measurable`, `sigma_algebra_measurable`,
    `sigma_algebraC`
  + definition `measure_restr`, lemma `measure_restrE`
  + definition `g_measurableType`
  + lemmas `measurable_g_measurableTypeE`
  + lemmas `measurable_fun_id`, `measurable_fun_comp`, `eq_measurable_fun`, `measurable_fun_cst`,
    `measurable_funU`, `measurable_funS`,  `measurable_fun_ext`, `measurable_restrict`
  + definitions `preimage_class` and `image_class`
  + lemmas `preimage_class_measurable_fun`, `sigma_algebra_preimage_class`, `sigma_algebra_image_class`,
    `sigma_algebra_preimage_classE`, `measurability`
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
  + lemmas `covered_byP`, `covered_by_finite`, `covered_by_countable`,
    `measure_le0`, `content_sub_additive`, `content_sub_fsum`,
    `content_ring_sup_sigma_additive`, `content_ring_sigma_additive`, `ring_sigma_sub_additive`,
    `ring_sigma_additive`, `measure_sigma_sub_additive`, `measureIl`, `measureIr`,
    `subset_measure0`, `measureUfinr`, `measureUfinl`, `eq_measureU`, `null_set_setU`
  + lemmas `g_salgebra_measure_unique_trace`, `g_salgebra_measure_unique_cover`, `g_salgebra_measure_unique`,
    `measure_unique`, `measurable_mu_extE`, `Rmu_ext`, `measurable_Rmu_extE`,
    `sub_caratheodory`
  + definition `Hahn_ext`, canonical `Hahn_ext_measure`, lemma `Hahn_ext_sigma_finite`, `Hahn_ext_unique`,
    `caratheodory_measurable_mu_ext`
  + definitions `preimage_classes`, `prod_measurable`, `prod_measurableType`
  + lemmas `preimage_classes_comp`, `measurableM`, `measurable_prod_measurableType`, `measurable_prod_g_measurableTypeR`,
    `measurable_prod_g_measurableType`, `prod_measurable_funP`, `measurable_fun_prod1`, `measurable_fun_prod2`
- in `functions.v`:
  + definitions `set_fun`, `set_inj`
  + mixin `isFun`, structure `Fun`, notations `{fun ... >-> ...}`, `[fun of ...]`
    * field `funS` declared as a hint
  + mixin `OInv`, structure `OInversible`, notations `{oinv ... >-> ...}`, `[oinv of ...]`, `'oinv_ ...`
  + structure `OInvFun`, notations `{oinvfun ... >-> ...}`, `[oinvfun of ...]`
  + mixin `OInv_Inv`, factory `Inv`, structure `Inversible`, notations `{inv ... >-> ...}`, `[inv of ...]`, notation `^-1`
  + structure `InvFun`, notations `{invfun ... >-> ...}`, `[invfun of ...]`
  + mixin `OInv_CanV` with field `oinvK` declared as a hint, factory `OCanV`
  + structure `Surject`, notations `{surj ... >-> ...}`, `[surj of ...]`
  + structure `SurjFun`, notations `{surjfun ... >-> ...}`, `[surjfun of ...]`
  + structure `SplitSurj`, notations `{splitsurj ... >-> ...}`, `[splitsurj of ...]`
  + structure `SplitSurjFun`, notations `{splitsurjfun ... >-> ...}`, `[splitsurjfun of ...]`
  + mixin `OInv_Can` with field `funoK` declared as a hint, structure `Inject`, notations `{inj ... >-> ...}`, `[inj of ...]`
  + structure `InjFun`, notations `{injfun ... >-> ...}`, `[injfun of ...]`
  + structure `SplitInj`, notations `{splitinj ... >-> ...}`, `[splitinj of ...]`
  + structure `SplitInjFun`, notations `{splitinjfun ... >-> ...}`, `[splitinjfun of ...]`
  + structure `Bij`, notations `{bij ... >-> ...}`, `[bij of ...]`
  + structure `SplitBij`, notations `{splitbij ... >-> ...}`, `[splitbij of ...]`
  + module `ShortFunSyntax` for shorter notations
  + notation `'funS_ ...`
  + definition and hint `fun_image_sub`
  + definition and hint `mem_fun`
  + notation `'mem_fun_ ...`
  + lemma `some_inv`
  + notation `'oinvS_ ...`
  + variant `oinv_spec`, lemma and hint `oinvP`
  + notation `'oinvP_ ...`
  + lemma and hint `oinvT`, notation `'oinvT_ ...`
  + lemma and hint `invK`, notation `'invK_ ...`
  + lemma and hint `invS`, notation `'invS_ ...`
  + notation `'funoK_ ...`
  + definition `inj` and notation `'inj_ ...`
  + definition and hint `inj_hint`
  + lemma and hint `funK`, notation `'funK_ ...`
  + lemma `funP`
  + factories `Inv_Can`, `Inv_CanV`
  + lemmas `oinvV`, `surjoinv_inj_subproof`, `injoinv_surj_subproof`, `invV`, `oinv_some`,
    `some_canV_subproof`, `some_fun_subproof`, `inv_oapp`, `oinv_oapp`, `inv_oappV`,
    `oapp_can_subproof`, `oapp_surj_subproof`, `oapp_fun_subproof`, `inv_obind`, `oinv_obind`,
    `inv_obindV`, `oinv_comp`, `some_comp_inv`, `inv_comp`, `comp_can_subproof`, `comp_surj_subproof`,
  + notation `'totalfun_ ...`
  + lemmas `oinv_olift`, `inv_omap`, `oinv_omap`, `omapV`
  + factories `canV`, `OInv_Can2`, `OCan2`, `Can`, `Inv_Can2`, `Can2`, `SplitInjFun_CanV`, `BijTT`
  + lemmas `surjective_oinvK`, `surjective_oinvS`, coercion `surjective_ocanV`
  + definition and coercion `surjection_of_surj`, lemma `Psurj`, coercion `surjection_of_surj`
  + lemma `oinv_surj`, lemma and hint `surj`, notation `'surj_`
  + definition `funin`, lemma `set_fun_image`, notation `[fun ... in ...]`
  + definition `split_`, lemmas `splitV`, `splitis_inj_subproof`, `splitid`, `splitsurj_subproof`,
    notation `'split_`, `split`
  + factories `Inj`, `SurjFun_Inj`, `SplitSurjFun_Inj`
  + lemmas `Pinj`, `Pfun`, `injPfun`, `funPinj`, `funPsurj`, `surjPfun`, `Psplitinj`, `funPsplitinj`,
    `PsplitinjT`, `funPsplitsurj`, `PsplitsurjT`
  + definition `unbind`
  + lemmas `unbind_fun_subproof`, `oinv_unbind`, `inv_unbind_subproof`, `inv_unbind`, `unbind_inj_subproof`,
    `unbind_surj_subproof`, `odflt_unbind`, `oinv_val`, `val_bij_subproof`, `inv_insubd`
  + definition `to_setT`, lemma `inv_to_setT`
  + definition `subfun`, lemma `subfun_inj`
  + lemma `subsetW`, definition `subsetCW`
  + lemmas `subfun_imageT`, `subfun_inv_subproof`
  + definition `seteqfun`, lemma `seteqfun_can2_subproof`
  + definitions `incl`, `eqincl`, lemma `eqincl_surj`, notation `inclT`
  + definitions `mkfun`, `mkfun_fun`
  + definition `set_val`, lemmas `oinv_set_val`, `set_valE`
  + definition `ssquash`
  + lemma `set0fun_inj`
  + definitions `finset_val`, `val_finset`
  + lemmas `finset_valK`, `val_finsetK`
  + definition `glue`, `glue1`, `glue2`, lemmas `glue_fun_subproof`, `oinv_glue`, `some_inv_glue_subproof`,
    `inv_glue`, `glueo_can_subproof`, `glue_canv_subproof`
  + lemmas `inv_addr`, `addr_can2_subproof`
  + lemmas `empty_can_subproof`, `empty_fun_subproof`, `empty_canv_subproof`
  + lemmas `subl_surj`, `subr_surj`, `surj_epi`, `epiP`, `image_eq`, `oinv_image_sub`,
    `oinv_Iimage_sub`, `oinv_sub_image`, `inv_image_sub`, `inv_Iimage_sub`, `inv_sub_image`,
    `reindex_bigcup`, `reindex_bigcap`, `bigcap_bigcup`, `trivIset_inj`, `set_bij_homo`
  + definition and hint `fun_set_bij`
  + coercion `set_bij_bijfun`
  + definition and coercion `bij_of_set_bijection`
  + lemma and hint `bij`, notation `'bij_`
  + definition `bijection_of_bijective`, lemmas `PbijTT`, `setTT_bijective`,
    lemma and hint `bijTT`, notation `'bijTT_`
  + definition `patch`, lemmas `patchT`, `patchN`, `patchC`, `patch_inj_subproof`,
    notations `restrict`, `... \_ ...`, lemmas `preimage_restrict`, `comp_patch`,
    `patch_setI`, `patch_setT`, `restrict_comp`
  + definitions `sigL`, `sigLfun`, `valL_`, `valLfun_`
  + lemmas `sigL_isfun`, `valL_isfun`, `sigLE`, `eq_sigLP`, `eq_sigLfunP`, `sigLK`, `valLK`,
    `valLfunK`, `sigL_valL`, `sigL_valLfun\`, `sigL_restrict`, `image_sigL`, `eq_restrictP`
  + notations `'valL_ ...`, `'valLfun_ ...`, `valL`
  + definitions `sigR`, `valLr`, `valLr_fun`
  + lemmas `sigRK`, `sigR_funK`, `valLrP`, `valLrK`
  + lemmas `oinv_sigL`, `sigL_inj_subproof`, `sigL_surj_subproof`, `oinv_sigR`, `sigR_inj_subproof`,
    `sigR_surj_subproof`, `sigR_some_inv`, `inv_sigR`, `sigL_some_inv`, `inv_sigL`,
    `oinv_valL`, `oapp_comp_x`, `valL_inj_subproof`, `valL_surj_subproof`, `valL_some_inv`,
    `inv_valL`, `sigL_injP`, `sigL_surjP`, `sigL_funP`, `sigL_bijP`, `valL_injP`, `valL_surjP`,
    `valLfunP`, `valL_bijP`
  + lemmas `oinv_valLr`, `valLr_inj_subproof`, `valLr_surj_subproof`
  + definitions `sigLR`, `valLR`, `valLRfun`, lemmas `valLRE`, `valLRfunE`, `sigL2K`,
    `valLRK`, `valLRfun_inj`, `sigLR_injP`, `valLR_injP`, `sigLR_surjP`, `valLR_surjP`,
    `sigLR_bijP`, `sigLRfun_bijP`, `valLR_bijP`, `subsetP`
  + new lemmas `eq_set_bijLR`, `eq_set_bij`, `bij_omap`, `bij_olift`, `bij_sub_sym`,
   `splitbij_sub_sym`, `set_bij00`, `bij_subl`, `bij_sub`, `splitbij_sub`, `can2_bij`,
   `bij_sub_setUrl`, `bij_sub_setUrr`, `bij_sub_setUrr`, `bij_sub_setUlr`
  + definition `pinv_`, lemmas `injpinv_surj`, `injpinv_image`,
    `injpinv_bij`, `surjpK`, `surjpinv_image_sub`, `surjpinv_inj`, `surjpinv_bij`,
    `bijpinv_bij`, `pPbij_`, `pPinj_`, `injpPfun_`, `funpPinj_`
- in `fsbigop.v`:
  + notations `\big[op/idx]_(i \in A) f i`, `\sum_(i \in A) f i`
  + lemma `finite_index_key`
  + definition `finite_support`
  + lemmas `in_finite_support`, `no_finite_support`, `eq_finite_support`
  + variant `finite_support_spec`
  + lemmas  `finite_supportP`, `eq_fsbigl`, `eq_fsbigr`,
    `fsbigTE`, `fsbig_mkcond`, `fsbig_mkcondr`, `fsbig_mkcondl`, `bigfs`,
    `fsbigE`, `fsbig_seq`, `fsbig1`, `fsbig_dflt`, `fsbig_widen`, `fsbig_supp`,
    `fsbig_fwiden`, `fsbig_set0`, `fsbig_set1`, `full_fsbigID`, `fsbigID`, `fsbigU`,
    `fsbigU0`, `fsbigD1`, `full_fsbig_distrr`, `fsbig_distrr`, `mulr_fsumr`, `mulr_fsuml`,
    `fsbig_ord`, `fsbig_finite`, `reindex_fsbig`, `fsbig_image`, `reindex_inside`,
    `reindex_fsbigT`, notation `reindex_inside_setT`
  + lemmas `ge0_mule_fsumr`, `ge0_mule_fsuml`, `fsbigN1`, `fsume_ge0`, `fsume_le0`,
    `fsume_gt0`, `fsume_lt0`, `pfsume_eq0`, `fsbig_setU`, `pair_fsum`, `exchange_fsum`,
    `fsum_split`
- in `mathcomp_extra.v`:
  + lemma `all_sig2_cond`
  + definition `olift`
  + lemmas `obindEapp`, `omapEbind`, `omapEapp`, `oappEmap`, `omap_comp`, `oapp_comp`,
    `oapp_comp_f`, `olift_comp`, `compA`, `can_in_pcan`, `pcan_in_inj`, `can_in_comp`,
    `pcan_in_comp`, `ocan_comp`, `pred_omap`, `ocan_in_comp`, `eqbLR`, `eqbRL`
  + definition `opp_fun`, notation `\-`
  + definition `mul_fun`, notation `\*`
  + definition `max_fun`, notation `\max`
  + lemmas `gtr_opp`, `le_le_trans`
  + notations `eqLHS`, `eqRHS`, `leLHS`, `leRHS`, `ltLHS`, `lrRHS`
  + inductive `boxed`
  + lemmas `eq_big_supp`, `perm_big_supp_cond`, `perm_big_supp`
  + lemmma `mulr_ge0_gt0`
  + lemmas `lt_le`, `gt_ge`
  + coercion `pair_of_interval`
  + lemmas `ltBSide`, `leBSide`
  + multirule `lteBSide`
  + lemmas `ltBRight_leBLeft`, `leBRight_ltBLeft`
  + multirule `bnd_simp`
  + lemmas `itv_splitU1`, `itv_split1U`
  + definition `miditv`
  + lemmas `mem_miditv`, `miditv_bnd2`, `miditv_bnd1`
  + lemmas `predC_itvl`, `predC_itvr`, `predC_itv`
- in `set_interval.v`:
  + definition `neitv`
  + lemmas `neitv_lt_bnd`, `set_itvP`, `subset_itvP`, `set_itvoo`, `set_itvco`, `set_itvcc`,
    `set_itvoc`, `set_itv1`, `set_itvoo0`, `set_itvoc0`, `set_itvco0`, `set_itv_infty_infty`, `set_itv_o_infty`,
    `set_itv_c_infty`, `set_itv_infty_o`, `set_itv_infty_c`, `set_itv_pinfty_bnd`,
    `set_itv_bnd_ninfty`
  + multirules `set_itv_infty_set0`, `set_itvE`
  + lemmas `setUitv1`, `setU1itv`
  + lemmas `neitvE`, `neitvP`, `setitv0`
  + lemmas `set_itvI`
  + lemmas and hints `has_lbound_itv`, `has_ubound_itv`, `hasNlbound_itv`, `hasNubound_itv`,
    `has_sup_half`, `has_inf_half`
  + lemmas `opp_itv_bnd_infty`, `opp_itvoo`,
    `sup_itv`, `inf_itv`, `sup_itvcc`, `inf_itvcc`
    `setCitvl`, `setCitvr`, `setCitv`
  + lemmas `set_itv_splitD`, `set_itvK`, `RhullT`, `RhullK`,
    `itv_c_inftyEbigcap`, `itv_bnd_inftyEbigcup`, `itv_o_inftyEbigcup`, `set_itv_setT`,
    `set_itv_ge`
  + definitions `conv`, `factor`
  + lemmas `conv_id`, `convEl`, `convEr`, `conv10`, `conv0`, `conv1`, `conv_sym`,
    `conv_flat`, `factorl`, `factorr`, `factor_flat`, `mem_1B_itvcc`, `factorK`,
    `convK`, `conv_inj`, `conv_bij`, `factor_bij`, `leW_conv`, `leW_factor`,
    `le_conv`, `le_factor`, `lt_conv`, `lt_factor`
  + definition `ndconv`
  + lemmas `ndconvE`, `conv_itv_bij`, `conv_itv_bij`, `factor_itv_bij`, `mem_conv_itv`,
    `mem_factor_itv`, `mem_conv_itvcc`, `range_conv`, `range_factor`, `Rhull_smallest`,
    `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`
  + coercion `ereal_of_itv_bound`
  + lemmas `le_bnd_ereal`, `lt_ereal_bnd`, `neitv_bnd1`, `neitv_bnd2`, `Interval_ereal_mem`,
    `ereal_mem_Interval`, `trivIset_set_itv_nth`
  + definition `disjoint_itv`
  + lemmas `disjoint_itvxx`, `lt_disjoint`, `disjoint_neitv`, `disj_itv_Rhull`
- new file `lebesgue_measure.v`
- new file `lebesgue_integral.v`
- in `ereal.v`:
  + lemmas `lte_suble_addr`, `lte_suble_addl`, `lte_subre_addr`,
    `lee_subre_addr`, `lee_suble_addr`, `lte_dsuble_addr`,
    `lte_dsuble_addl`, `lte_dsubre_addr`, `lee_dsubre_addr`,
    `lee_dsuble_addr`

### Changed

- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`
- in `topology.v`:
  + generalize `connected_continuous_connected`, `continuous_compact`
  + arguments of `subspace`
- in `derive.v`:
  + generalize `EVT_max`, `EVT_min`, `Rolle`, `MVT`, `ler0_derive1_nincr`,
    `le0r_derive1_ndecr` with subspace topology
  + implicits of `cvg_at_rightE`, `cvg_at_leftE`
- in `sequences.v`:
  + `\sum` notations for extended real numbers now in `ereal_scope`
  + lemma `ereal_cvg_sub0` is now an equivalence
- in `topology.v`:
  + definition `connected_component`
- in `boolp.v`:
  + `equality_mixin_of_Type`, `choice_of_Type` -> see `classicalType`
- in `esum.v` (was `csum.v`):
  + lemma `esum_ge0` has now a weaker hypothesis
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
  + definition `surjective` moved to `functions.v` and renamed `set_surj`
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
  + definition `inverse` changed to `pinv_`, see `functions.v`
  + lemma `inj_of_bij` moved to `functions.v` and renamed to `set_bij_inj`
  + lemma `sur_of_bij` moved to `functions.v` and renamed to `set_bij_surj`
  + lemma `sub_of_bij` moved to `functions.v` and renamed to `set_bij_sub`
  + lemma `set_bijective_D1` moved to `functions.v` and renamed to `bij_II_D1`
  + lemma `injective_left_inverse` moved to `functions.v` and changed to `pinvKV`
  + lemma `injective_right_inverse` moved to `functions.v` and changed to `pinvK`
  + lemmas `image_nat_maximum`, `fset_nat_maximum` moved to `mathcomp_extra.v`
  + lemmas `enum0`, `enum_recr` moved to `mathcomp_extra.v` and renamed to `enum_ord0`, `enum_ordS`
  + lemma `in_inj_comp` moved to `mathcomp_extra.v`
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
- in `ereal.v`:
  + lemmas `big_nat_widenl`, `big_geq_mkord` moved to `mathcomp_extra.v`
- moved from `normedtype.v` to `mathcomp_extra.v`:
  + lemmas `ler_addgt0Pr`, `ler_addgt0Pl`, `in_segment_addgt0Pr`, `in_segment_addgt0Pl`,
- moved from `posnum.v` to `mathcomp_extra.v`:
  + lemma `splitr`
- moved from `measure.v` to `sequences.v`
  + lemma `cvg_geometric_series_half`
  + lemmas `realDe`, `realDed`, `realMe`, `nadde_eq0`, `padde_eq0`,
    `adde_ss_eq0`, `ndadde_eq0`, `pdadde_eq0`, `dadde_ss_eq0`,
    `mulrpinfty_real`, `mulpinftyr_real`, `mulrninfty_real`,
    `mulninftyr_real`, `mulrinfty_real`

### Changed

- in `ereal.v`:
  + lemmas `abse_ge0`, `gee0_abs`, `gte0_abs`, `lee0_abs`, `lte0_abs`,
    `mulN1e`, `muleN1` are generalized from `realDomainType` to
    `numDomainType`

### Renamed

- in `topology.v`:
  + `closedC` -> `open_closedC`
  + `openC` -> `closed_openC`
  + `cvg_restrict_dep` -> `cvg_sigL`
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
- file `csum.v` renamed to `esum.v` with the following renamings:
  + `\csum` -> `\esum`
  + `csum` -> `esum`
  + `csum0` -> `esum_set0`
  + `csum_ge0` -> `esum_ge0`
  + `csum_fset` -> `esum_fset`
  + `csum_image` -> `esum_image`
  + `csum_bigcup` -> `esum_bigcup`

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`
- in `csum.v`:
  + lemmas `fsets_img`, `fsets_ord`, `fsets_ord_nat`, `fsets_ord_subset`, `csum_bigcup_le`,
    `le_csum_bigcup`
- in `classical_sets.v`:
  + lemma `subsetU`
  + definition `patch`, notations `restrict` and `... \|_ ...`
  + definition `restrict_dep`, `extend_up`, lemma `restrict_depE`
- in `cardinality.v`:
  + lemma `surjective_image`, `surjective_image_eq0`
  + lemma `surjective_right_inverse`,
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
  + definition `uncurry`

### Infrastructure

### Misc
