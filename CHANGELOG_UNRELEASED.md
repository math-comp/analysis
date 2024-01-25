# Changelog (unreleased)

## [Unreleased]

### Added

- in `cantor.v`:
  + definition `pointed_principal_filter`, instances using `Pointed.on` and `hasNbhs.Build`
  + definition `pointed_discrete_topology`
  + lemma `discrete_pointed`
  + lemma `discrete_bool_compact`

- in `charge.v`:
  + `cscale` instances using `SigmaFinite_isFinite.Build` and `isAdditiveCharge.Build`

- in `convex.v`:
  + definition `convex_lmodType` with instances using `Choice.on` and `isConvexSpace.Build`
  + definition `convex_realDomainType` with instance using `isConvexSpace.Build`

- in `constructive_ereal.v`:
  + definition `dEFin`
  + notations `%:dE`, `%:E` (`ereal_dual_scope`)
  + notation `\bar^d ...` (`type_scope`) for dual extended real numbers
  + instance using `isNmodule.Build` for `\bar`
  + instances using `Choice.on` and `isNmodule.Build` for `\bar^d`
  + lemma `EFin_semi_additive`
  + lemmas `dEFinE`, `dEFin_semi_additive`
  + instance using `isSemiAdditive.Build` for `\bar^d`
  + canonical `dEFin_snum`

- in `derive.v`:
  + lemma `cvg_at_rightE`, `cvg_at_leftE`

- in `lebesgue_integral.v`:
  + mixin `isNonNegFun`, notations `{nnfun _ >-> _}`, `[nnfun of _]`
  + section `ring`
    * lemmas `fimfun_mulr_closed`, instances using `GRing.isMulClosed.Build`,
      `[SubZmodule_isSubRing of ... by <:]`
    * lemmas `fimfunM`, `fimfun1`, `fimfun_prod`, `fimfunX`,
    * lemma `indic_fimfun_subproof`, instance using `indic_fimfun_subproof`
    * definition `indic_fimfun`
    * instance using `FImFun.copy`, definition `scale_fimfun`
  + section `comring`
    * instance using `[SubRing_isSubComRing of ... by <:]`
	* instance using `FImFun.copy`
  + lemmas `fimfunE`, `fimfunEord`, `trivIset_preimage1`, `trivIset_preimage1_in`
  + section `fimfun_bin`
    * lemma `max_fimfun_subproof`, instance using `max_fimfun_subproof`
  + factory `FiniteDecomp`

- in `lebesgue_stieltjes_measure.v`:
  + instance on `ocitv_type` using `Pointed.on`

- in `normedtype.v`:
  + definition `urysohnType` with instances using `Pointed.on` and `isUniform.Build`

- in `reals.v`:
  + definition `Rint_pred`

- in `topology.v`
  + definition `set_system`, identity coercion `set_system_to_set`
    with instances using `Equality.on`, `Choice.on`, `Pointed.on`,
	`isFiltered.Build`
  + mixin `selfFiltered`, factory `hasNbhs`, structure `Nbhs`,
    type `nbhsType`
  + instance for matrices using `selfFiltered.Build`
  + lemmas `cvg_in_ex`, `cvg_inP`, `cvg_in_toP`, `dvg_inP`, `cvg_inNpoint`,
    `eq_is_cvg_in`
  + notations `E @[ x \oo ]`, `limn`, `cvgn`
  + definition `continuous_at`
  + definitions `weak_topology`, `sup_topology`, `prod_topology`
  + definition `prod_topo_apply`
  + definition `discrete_topology`
  + instead of `zmodType` using `isPointed.Build`
  + definition `pointwise_cvgE`,
    instance using `Uniform.copy` for `{ptws _ -> _}`
  + definition `compact_open_of_nbhs`, lemmas `compact_openK_nbhsE_subproof`,
    `compact_openK_openE_subproof`

### Changed

- in `boolp.v`:
  + in lemma `gen_choiceMixin`: `Choice.mixin_of` -> `hasChoice`
  + in definition `gen_eqMixin`: `EqMixin` -> `hasDecEq.Build`
  + canonical `dep_arrow_eqType` -> instance using `gen_eqMixin`
  + canonical `dep_arrow_choiceType` -> instance using `gen_choiceMixin`
  + canonical `Prop_eqType` -> instance using `gen_eqMixin`
  + canonical `Prop_choiceType` -> instance using `gen_choiceMixin`
  + canonical `classicType_eqType` -> instance using `gen_eqMixin`
  + canonical `classicType_choiceType` -> instance using `gen_choiceMixin`
  + canonical `eclassicType_eqType` -> instance using `Equality.copy`
  + canonical `eclassicType_choiceType` -> instance using `gen_choiceMixin`
  + definition `porderMixin` and canonical `porderType` -> instance using `isPOrder.Build`
  + definition `latticeMixin` and canonical `latticeType` -> instance using `POrder_isLattice.Build`

- in `cardinality.v`:
  + canonical `rat_pointedType` -> instance using `isPointed.Build`
  + canonical `fimfun_subType` -> instance using `isSub.Build`
  + definition `fimfuneqMixin` and canonical `fimfuneqType` -> instance using `[Equality of ... by <:]`
  + definition `fimfunchoiceMixin` and canonical `fimfunchoiceType` -> instance using `[Choice of ... by <:]`
  + canonicals `fimfun_add`, `fimfun_zmod`, `fimfun_zmodType`, and definition `fimfun_zmodMixin` ->
    instances using `isZmodClosed.Build` and `[SubChoice_isSubZmodule of ... <:]`

- in `classical_sets.v`:
  + canonicals
    `setU_monoid`, `setU_comoid`, `setU_mul_monoid`, `setI_monoid`,
    `setI_comoid`, `setI_mul_monoid`, `setU_add_monoid`, `setI_add_monoid`
	-> instances using
	`isComLaw.Build`, `isMulLaw.Build`, `isComLaw.Build`, `isMulLaw.Build`, `isAddLaw.Build`, `isAddLaw.Build`
  + module `Pointed` (packed class) -> mixin `isPointed`, structure `Pointed`
  + canonical `arrow_pointedType` and definition `dep_arrow_pointedType` -> instance using `isPointed.Build`
  + canonicals
    `unit_pointedType`, `bool_pointedType`, `Prop_pointedType`, `nat_pointedType`,
	`prod_pointedType`, `matrix_pointedType`, `option_pointedType`, `pointed_fset`
	-> instances using
	`isPointed.Build`
  + module `Empty` (packed class) -> mixin `isEmpty`, structure `Empty`, factories `Choice_isEmpty`, `Type_isEmpty`
  + definition `False_emptyMixin` and canonicals `False_eqType`,
    `False_choiceType`, `False_countType`, `False_finType`, `False_emptyType` ->
    instance using `Type_isEmpty.Build`
  + definition `void_emptyMixin` and canonical `void_emptyType` -> instance using `isEmpty.Build`
  + definition `orderMixin` and canonicals `porderType`, `latticeType`, `distrLatticeType` ->
    instances using `Choice.copy` and `isMeetJoinDistrLattice.Build`
  + canonicals `bLatticeType`, `tbLatticeType`, `bDistrLatticeType`, `tbDistrLatticeType` ->
    instances using `hasBottom.Build` and `hasTop.Build`
  + canonical `cbDistrLatticeType` -> instance using `hasRelativeComplement.Build`
  + canonical `ctbDistrLatticeType` -> instance using `hasComplement.Build`

- in `functions.v`:
  + notation `split`
  + notation `\_` moved from `fun_scope` to `function_scope`
  + notations `pinv`, `pPbij`, `pPinj`, `injpPfun`, `funpPinj`
  + in definition `fct_zmodMixin`: `ZmodMixin` -> `isZmodule.Build`
  + canonical `fct_zmodType` -> instance using `fct_zmodMixin`
  + in definition `fct_ringMixin`: `RingMixin` -> `Zmodule_isRing.Build`
  + canonical `fct_ringType` -> instance using `fct_ringMixin`
  + canonical `fct_comRingType` ->
    definition and instance using `Ring_hasCommutativeMul.Build` and `fct_comRingType`
  + definition `fct_lmodMixin` and canonical `fct_lmodType` ->
    definition `fct_lmodMixin` and instance using `fct_lmodMixin`

- in `Rstruct.v`:
  + canonicals `R_eqMixin`, `R_eqType` -> instance using `hasDecEq.Build`
  + definition `R_choiceMixin` and canonical `R_choiceType` -> instance using `hasChoice.Build`
  + definition `R_zmodMixin` and canonical `R_zmodType` -> instance using `isZmodule.Build`
  + definition `R_ringMixin` and canonicals `R_ringType`, `R_comRingType` ->
    instances using `Zmodule_isRing.Build`, `Ring_hasCommutativeMul.Build`
  + canonicals `Radd_monoid`, `Radd_comoid` -> instance using `isComLaw.Build`
  + canonicals `Rmul_monoid`, `Rmul_comoid` -> instance using `isComLaw.Build`
  + canonical `Rmul_mul_law` -> instance using `isMulLaw.Build`
  + canonical `Radd_add_law` -> instance using `isAddLaw.Build`
  + definition `R_unitRingMixin` and canonical `R_unitRing` -> instance using `Ring_hasMulInverse.Build`
  + canonicals `R_comUnitRingType` and `R_idomainType` ->
    instance using `ComUnitRing_isIntegral.Build`
  + in lemma `R_fieldMixin`: `GRing.Field.mixin_of` -> `GRing.field_axiom`
  + definition `Definition` and canonical `R_fieldType` -> instance using `UnitRing_isField.Build`
  + definition `R_numMixin`, canonicals `R_porderType`, `R_numDomainType`, `R_normedZmodType`, `R_numFieldType`
    -> instance using `IntegralDomain_isNumRing.Build`
  + in lemma `R_total`: `totalPOrderMixin` -> `total`
  + canonicals `R_latticeType`, `R_distrLatticeType`, `R_orderType`, `R_realDomainType`, `R_realFieldType`
    -> instance using `POrder_isTotal.Build`
  + in lemmas `Rarchimedean_axiom`, `Rreal_closed_axiom`: `R_numDomainType` -> `[the numDomainType of R : Type]`
  + canonical `R_realArchiFieldType` -> instance using `RealField_isArchimedean.Build`
  + canonical `R_rcfType` -> instance using `RealField_isClosed.Build`
  + definition `real_realMixin` and canonical `real_realType` -> instance using `ArchimedeanField_isReal.Build`

- in `altreals/discrete.v`:
  + canonical `pred_sub_subTypeP` -> instance using `[isSub for ...]`
  + definition `pred_sub_eqMixin` and canonical `pred_sub_eqType` ->
    instance using `[Equality of ... by <:]`
  + definition `pred_sub_choiceMixin` and canonical `pred_sub_choiceType` ->
    instance using `[Choice of ... <:]`
  + definition `pred_sub_countMixin` and `pred_sub_countType` ->
    instance using `[Countable of ... by <:]`
  + definitions `countable_countMixin` and `countable_countType` -> `countable_countMixin`
  + definitions `countable_choiceMixin` and `countable_choiceType` -> `countable_choiceMixin`

- in `altreals/xfinmap.v`:
  + in lemmas `enum_fset0` and `enum_fset1`: notation `[fintype of ...]` -> type constraint `... : finType`

- in `cantor.v`:
	+ in definition `tree_of` and lemma `cantor_like_finite_prod`:
	  `pointed_discrete` -> `pointed_discrete_topology`

- in `constructive_ereal.v`:
  + definition `ereal_eqMixin` and canonical `ereal_eqType` -> instance using `hasDecEq.Build`
  + definition `ereal_choiceMixin` and canonical `ereal_choiceType` -> instance using `Choice.copy`
  + definition `ereal_countMixin` and `ereal_countType` -> instance using `PCanIsCountable`
  + definition `ereal_porderMixin` and canonical `Choice.copy` -> instance using `isPOrder.Build`
  + in lemma `le_total_ereal` : `le_total_ereal` -> `total`
  + canonicals `ereal_latticeType`, `ereal_distrLatticeType`, `ereal_orderType`, `ereal_blatticeType`,
    `ereal_tblatticeType`, lemmas `ereal_blatticeMixin`, `ereal_blatticeMixin` ->
    instances using `POrder_isTotal.Build`, `hasBottom.Build`, `hasTop.Build`
  + canonicals `adde_monoid`, `adde_comoid`, `mule_mulmonoid` -> instance using `isMulLaw.Build`
  + notations `maxe`, `mine`: `fun_scope` -> `function_scope`
  + canonicals `mule_monoid`, `mule_comoid` -> instance using `isComLaw.Build`
  + canonicals `maxe_monoid`, `maxe_comoid` -> instance using `isLaw.Build`

- in `derive.v`
  + in notation `'d`, `differentiable`, `is_diff`: `[filter of ...]` -> `nbhs F`
  + canonical `mulr_linear` -> instance using `isLinear.Build`
  + canonical `mulr_rev_linear` -> instance using `isLinear.Build`
  + canonical `mulr_bilinear` -> lemma `mulr_is_bilinear` and instance using `bilinear_isBilinear.Build`
  + `set (set ...)` -> `set_system ...`

- in `ereal.v`:
  + canonical `ereal_pointed` -> instance using `isPointed.Build`
  + definitions `ereal_dnbhs`, `ereal_nbhs` -> now use `set_system`
  + canonical `ereal_ereal_filter` -> instance using `hasNbhs.Build`
  + definition `ereal_topologicalMixin`, canonical `ereal_topologicalType`,
    definitions `ereal_pseudoMetricType_mixin`, `ereal_uniformType_mixin`,
	canonicals `ereal_uniformType`, `ereal_pseudoMetricType` ->
	instance using `Nbhs_isPseudoMetric.Build`

- in `esum.v`:
  + several occurrences of `cvg`/`lim` changed to `cvgn`/`limn` and
    usages of the notation `X --> Y` changed to `X @ F --> Y` (with an explicit filter)
    * `is_cvg_pseries_inside_norm`
	* `is_cvg_pseries_inside`
	* `pseries_diffs_equiv`
    * `is_cvg_pseries_diffs_equiv`
	* `pseries_snd_diffs`
	* `expRE`
    * `dvg_riemannR`

- in `forms.v`:
  + module `Bilinear` (packed class) -> mixin `isBilinear`, structure `Bilinear`,
    definition `bilinear_for`, factory `bilinear_isBilinear`, new module `Bilinear`
	containing the definition `map`
  + canonical `mulmx_bilinear` -> lemma `mulmx_is_bilinear` and instance using
    `bilinear_isBilinear.Build`

- in `itv.v`:
  + canonical `itv_subType` -> instance using `[isSub for ... ]`
  + definitions `itv_eqMixin`, `itv_choiceMixin` and canonicals `itv_eqType`, `itv_choiceType`
    -> instance using `[Choice of ... by <:]`
  + definition `itv_porderMixin` and canonical `itv_porderType` -> instance using
    `[SubChoice_isSubPOrder of ... by <: with ...]`

- in `kernel.v`:
  + notation `X --> Y` changed to `X @ F --< Y`
	* `measurable_fun_xsection_integral`
  + definition `prob_pointed` and canonical `probability_ptType` ->
    instance using `isPointed.Build`
  + canonicals `probability_eqType`, `probability_choiceType` ->
    instance using `gen_eqMixin` and `gen_choiceMixin`

- in `landau.v`:
  + now use `set_system`
    * structures `littleo_type`, `bigO_type`, `bigOmega_type`, `bigTheta_type`
	* lemmas `littleo_class`, `littleoE`, `littleo`, `bigO_exP`, `bigO_class`,
	  `bigO_clone`, `bigOP`, `bigOE`, `bigOmegaP`, `bigThetaP`
	* definitions `littleo_clone`, `the_littleo`, `littleoP`, `the_bigO`,
	  `bigOmega_clone`, `the_bigOmega`, `is_bigOmega`, `bigTheta_clone`,
	  `is_bigTheta`
	* variants `littleo_spec`, `bigOmega_spec`, `bigTheta_spec`
	* notation `PhantomF`
	* facts `is_bigOmega_key`, `is_bigTheta_key`
	* canonicals `the_littleo_littleo`, `the_bigO_bigO`, `the_littleo_bigO`,
	  `is_bigOmega_keyed`, `the_bigOmega_bigOmega`, `is_bigTheta_keyed`,
	  `the_bigTheta_bigTheta`
  + canonical `littleo_subtype` -> instance using `[isSub for ...]`
  + canonical `bigO_subtype` -> instance using `[isSub for ...]`
  + in `linear_for_continuous`:
    * `GRing.Scale.op s_law` -> `GRing.Scale.Law.sort`
	* argument `s_law` removed
  + canonical `bigOmega_subtype` -> instance using `[isSub for ...]`
  + canonical `bigTheta_subtype` -> instance using `[isSub for ...]`

- in `lebesgue_integral.v`:
  + canonical `mfun_subType` -> instance using `isSub.Build`
  + definitions `mfuneqMixin`, `mfunchoiceMixin`, canonicals `mfuneqType`,
    `mfunchoiceType` -> instance using `[Choice of ... by <:]`
  + canonicals `mfun_add`, `mfun_zmod`, `mfun_mul`, `mfun_subring`,
    `mfun_zmodType`, `mfun_ringType`, `mfun_comRingType`,
    definitions `mfun_zmodMixin`, `mfun_ringMixin`, `mfun_comRingMixin`,
	-> instances using `GRing.isSubringClosed.Build` and `[SubChoice_isSubComRing of ... <:]`
  + canonical `sfun_subType` -> instance using `isSub.Build`
  + definitions `sfuneqMixin`, `sfunchoiceMixin`,
    canonicals `sfuneqType`, `sfunchoiceType` ->
	instance using `[Choice of .. by <:]`
  + canonicals `sfun_add`, `sfun_zmod`, `sfun_mul`, `sfun_subring`, `sfun_zmodType`,
    `sfun_ringType`, `sfun_comRingType`,
    definitions `sfun_zmodMixin`, `sfun_ringMixin`, `sfun_comRingMixin`
	-> instances using `GRing.isSubringClosed.Build` and `[SubChoice_isSubComRing of ... by <:]`
  + now use `cvgn`/`limn` instead of `cvg`/`lim`:
    * lemmas `is_cvg_sintegral`, `nd_sintegral_lim_lemma`, `nd_sintegral_lim`, `nd_ge0_integral_lim`,
	  `dvg_approx`, `ecvg_approx`
  + filter now explicit in:
    * lemmas `approximation`, `approximation_sfun`, `cvg_monotone_convergence`

- in `lebesgue_measure.v`:
  + filter now explicit in lemmas `emeasurable_fun_cvg`,
    `ae_pointwise_almost_uniform`

- in `measure.v`
  + canonicals `salgebraType_eqType`, `salgebraType_choiceType`, `salgebraType_ptType`
    -> instance using `Pointed.on`
  + filter now explicit in:
    * definitions `sigma_additive`, `semi_sigma_additive`
	* lemmas `nondecreasing_cvg_mu`, `nonincreasing_cvg_mu`
  + canonicals `ring_eqType`, `ring_choiceType`, `ring_ptType` -> instance using `Pointed.on`

- in `misc/uniform_bigO.v`:
  + in definition `OuO`: `[filter of ...]` -> `nbhs ...`

- in `normedtype.v`:
  + module `PseudoMetricNormedZmodule` (packed class) ->
    mixin `NormedZmod_PseudoMetric_eq` (with field `pseudo_metric_ball_norm`),
	structure `PseudoMetricNormedZmod`
  + now use `set_system`:
    * definitions `pinfty_nbhs`, `ninfty_nbhs`, `dominated_by`, `strictly_dominated_by`,
	  `bounded_near`, `sub_klipschitz`, `lipschitz_on`, `sub_lipschitz`
	* lemmas `cvgrnyP`, `cvgenyP`, `fcvgrPdist_lt`, `cvgrPdist_lt`, `cvgrPdistC_lt`,
	  `cvgr_dist_lt`, `cvgr_distC_lt`, `cvgr_dist_le`, `cvgr_distC_le`, `cvgr0Pnorm_lt`,
	  `cvgr0_norm_lt`, `cvgr0_norm_le`, `cvgrPdist_le`, `cvgrPdist_ltp`, `cvgrPdist_lep`,
	  `cvgrPdistC_le`, `cvgrPdistC_ltp`, `cvgrPdistC_lep`, `cvgr0Pnorm_le`, `cvgr0Pnorm_ltp`,
	  `cvgr0Pnorm_lep`, `cvgr_norm_lt`, `cvgr_norm_le`, `cvgr_norm_gt`, `cvgr_norm_ge`,
	  `cvgr_neq0`, `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_gt`, `real_cvgr_ge`, `cvgr_lt`,
	  `cvgr_le`, `cvgr_gt`, `cvgr_ge`, `sub_dominatedl`, `sub_dominatedr`, `ex_dom_bound`,
	  `ex_strict_dom_bound`, `sub_boundedr`, `sub_boundedl`, `ex_bound`, `ex_strict_bound`,
	  `ex_strict_bound_gt0`, `klipschitzW`, `cvg_bounded`, `fcvgr2dist_ltP`, `cvgr2dist_ltP`,
	  `cvgr2dist_lt`
  + module `NormedModule` (packed class) ->
    mixin `PseudoMetricNormedZmod_Lmodule_isNormedModule`,
	structure `NormedModule`
  + module and section `regular_topology` -> section `regular_topology`
    with instances using `Num.NormedZmodule.on`, `NormedZmod_PseudoMetric_eq.Build`,
	`seudoMetricNormedZmod_Lmodule_isNormedModule.Build`
  + in module `numFieldNormedType`
	* `realType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`
	* `rcfType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`
	* `archiFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`
	* `realFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`, `Num.RealField.on`
	* `numClosedFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`, `Num.ClosedField.on`
	* `numFieldType` instances using `GRing.ComAlgebra.copy`, `Vector.copy`, `NormedModule.copy`, `Num.NumField.on`
  + in lemma `norm_lim_id`: now explicit use of `nbhs`
  + definition `matrix_PseudoMetricNormedZmodMixin` and canonical `matrix_normedModType`
    -> instance using `PseudoMetricNormedZmod_Lmodule_isNormedModule.Build`
  + definition `prod_pseudoMetricNormedZmodMixin` and canonical `prod_normedModType`
    -> instance using `PseudoMetricNormedZmod_Lmodule_isNormedModule.Build`
  + module `CompleteNormedModule` (packed class) -> structure `CompleteNormedModule`
  + canonicals `R_regular_completeType`, `R_regular_CompleteNormedModule` ->
    instance using `Uniform_isComplete.Build`
  + canonicals `R_completeType` and `R_CompleteNormedModule` -> instance using `Complete.on`
  + now use `cvgn` instead of `cvg`:
    * lemma `cvg_seq_bounded`

- "moved" from `normedtype.v` to `Rstruct.v`:
  + canonicals `R_pointedType`, `R_filteredType`, `R_topologicalType`, `R_uniformType`,
    `R_pseudoMetricType` -> instance using `PseudoMetric.copy`

- in `numfun.v`:
  + canonicals `fimfun_mul`, `fimfun_ring`, `fimfun_ringType`, definition `fimfun_ringMixin`
    -> instances using `GRing.isMulClosed.Build` and `[SubZmodule_isSubRing of ... by <:]`
  + definition `fimfun_comRingMixin`, canonical `fimfun_comRingType` ->
    instance using `[SubRing_isSubComRing of ... by <:]`

- in `prodnormedzmodule.v`:
  + definition `normedZmodMixin` and canonical `normedZmodType` ->
    instance using `Num.Zmodule_isNormed.Build`

- in `realfun.v`:
  + now explicitly display the filter in the notation `X --> Y`:
    * lemma s`cvg_at_rightP`, `cvg_at_leftP`, `cvge_at_rightP`, `cvge_at_leftP`

- in `reals.v`:
  + module `Real` (packed class) -> mixin `ArchimedeanField_isReal`
    with fields `sup_upper_bound_subdef`, `sup_adherent_subdef`,
	structure `Real`
  + canonicals `Rint_keyed`, `Rint_opprPred`, `Rint_addrPred`, `Rint_mulrPred`, `Rint_zmodPred`,
    `Rint_semiringPred`, `Rint_smulrPred`, `Rint_subringPred`
	-> instance using `GRing.isSubringClosed.Build`

- in `sequences.v`:
  + the lemmas and the notations (in particular, bigop notations) that were using
    `cvg` or `cvg (... @ \oo)`/`lim` are now using `cvgn`/`limn`
    and now explicitly mention the filter in the notation `X --> Y`

- in `signed.v`:
  + definitions `signed_subType`, `signed_choiceMixin`, `signed_porderMixin`, 
    canonicals `signed_eqMixin`, `signed_eqType`, `signed_choiceType`, `signed_porderType`
	-> instances using `[isSub for ...]` and `[POrder of ... by <:]`
  + in lemma `signed_le_total`: `totalPOrderMixin` -> `total`
  + canonicals `signed_latticeType`, `signed_distrLatticeType`, `signed_orderType`
    -> instance using `Order.POrder_isTotal.Build`

- in `summability.v`:
  + `totally` now uses `set_system`

- in `trigo.v`:
  + now make explicit mention of the filter:
    * definitions `sin`, `cos`
    * lemmas `cvg_series_cvg_series_group`, `lt_sum_lim_series`, `is_cvg_series_sin_coeff`,
	  `sinE`, `cvg_sin_coeff'`, `is_cvg_series_cos_coeff`, `cosE`, `cvg_cos_coeff'`

- in `topology.v`:
  + canonicals `linear_eqType`, `linear_choiceType` ->
    instances using `gen_eqMixin`, `gen_choiceMixin`
  + canonical `gen_choiceMixin` -> instance using `isPointed.Build`
  + module `Filtered` (packed class) -> mixin `isFiltered` with field `nbhs`,
    structure `Filtered`
  + now use `set_system`:
    * definitions `filter_from`, `filter_prod`, `cvg_to`, `type_of_filter`, `lim_in`,
	  `Build_ProperFilter`, `filter_ex`, `fmap`, `fmapi`, `globally`, `in_filter_prod`,
	  `within`, `subset_filter`, `powerset_filter_from`, `principal_filter`, `locally_of`,
	  `sup_subbase`, `cluster`, `compact`, `near_covering`, `near_covering_within`,
	  `compact_near`, `nbhs_`, `weak_ent`, `sup_ent`, `cauchy`, `cvg_cauchy`, `cauchy_ex.Build`,
	  `cauchy_ball`
	* classes `Filter`, `ProperFilter'`, `UltraFilter`
	* instances `fmap_proper_filter`, `fmapi_filter`, `fmapi_proper_filter`,
	  `filter_prod_filter`, `filter_prod1`, `filter_prod2`
	* record `in_filter`
	* structure `filter_on`
	* variant `nbhs_subspace_spec`
	* lemmas `nearE`, `eq_near`, `nbhs_filterE`, `cvg_refl`, `cvg_trans`, `near2_curry`,
	  `near_swap`, `filterP_strong`, `filter_nbhsT`, `nearT`, `filter_not_empty_ex`,
	  `filter_ex_subproof`, `filter_getP`, `near`, `nearW`, `filterE`, `filter_app`,
	  `filter_app2`, `filter_app3`, `filterS2`, `filterS3`, `nearP_dep`, `filter2P`,
	  `filter_ex2`, `filter_fromP`, `filter_fromTP`, `filter_bigIP`, `filter_forall`,
	  `filter_imply`, `fmapEP`, `fmapiE`, `cvg_id`, `appfilterP`, `cvg_app`, `cvgi_app`,
	  `cvg_comp`, `cvgi_comp`, `near_eq_cvg`, `eq_cvg`, `neari_eq_loc`, `cvg_near_const`,
	  `near_pair`, `near_map`, `near_map2`, `near_mapi`, `filter_pair_set`,
	  `filter_pair_near_of`, `cvg_pair`, `cvg_comp2`, `near_powerset_map`,
	  `near_powerset_map_monoE`, `cvg_fmap`, `continuous_cvg`, `continuous_is_cvg`,
	  `continuous2_cvg`, `cvg_near_cst`, `is_cvg_near_cst`, `cvg_cst`, `is_cvg_cst`,
	  `fmap_within_eq`, `cvg_image`, `cvg_fmap2`, `cvg_within_filter`, `cvg_app_within`,
	  `meets_openr`, `meets_openl`, `meetsxx`, `proper_meetsxx`, `ultra_cvg_clusterE`,
	  `ultraFilterLemma`, `compact_ultra`, `proper_image`, `in_ultra_setVsetC`,
	  `ultra_image`, `filter_finI`, `close_cvg`, `discrete_cvg`, `nbhs_E`, `cvg_closeP`,
	  `cvg_mx_entourageP`, `cvg_fct_entourageP`, `fcvg_ball2P`, `cvg_ball2P`, `cauchy_cvgP`,
	  `mx_complete`, `Uniform_isComplete.Build`, `cauchy_ballP`, `cauchy_exP`, `cauchyP`,
      `compact_cauchy_cvg`, `pointwise_cvgE`, `pointwise_uniform_cvg`, `cvg_sigL`, `uniform_restrict_cvg`,
	  `cvg_uniformU`, `cvg_uniform_set0`, `fam_cvgP`, `family_cvg_subset`,
	  `family_cvg_finite_covers`, `fam_cvgE`, `Nbhs_isTopological`, `compact_open_fam_compactP`,
      `compact_cvg_within_compact`, `nbhs_subspace`, `subspace_cvgP`, `uniform_limit_continuous`,
	  `uniform_limit_continuous_subspace`, `pointwise_compact_cvg`
	* `t` in module type `PropInFilterSig`
  + canonical `matrix_filtered` -> instance using `isFiltered.Build`
  + now use `nbhs` instead of `[filter of ...]`
    * notations `-->`, `E @[ x --> F ]`, `f @ F`, ```E `@[ x --> F ]```, ```f `@ G```,
	  `{ptws, F --> f }`
  + notation `lim` is now a definition
  + canonical `filtered_prod` -> instances using `isFiltered.Build`, `selfFiltered.Build`
  + now use `set_system` and also `nbhsType` instead of `filteredType ...`
    * lemmas `cvg_ex`, `cvgP`, `cvg_toP`, `dvgP`, `cvgNpoint`, `eq_is_cvg`
  + canonicals `filter_on_eqType`, `filter_on_choiceType`, `filter_on_PointedType`,
    `filter_on_FilteredType` -> instances using `gen_eqMixin`, `gen_choiceMixin`,
	`isPointed.Build`, `isFiltered.Build`
  + canonical `bool_discrete_filter` -> instance using `hasNbhs.Build`
  + module `Topological` (packed class) -> mixin `Nbhs_isTopological`,
    structure `Topological`, type `topologicalType`
	* definition `open` now a field of the mixin
  + notation `continuous` now uses definition `continuous_at`
  + section `TopologyOfFilter` -> factory `Nbhs_isNbhsTopological`
  + section `TopologyOfOpen` -> factory `Pointed_isOpenTopological`
  + section `TopologyOfBase` -> factory `Pointed_isBaseTopological`
  + section `TopologyOfSubbase` -> factory `Pointed_isSubBaseTopological`
  + definition `Pointed_isSubBaseTopological`,
    canonicals `nat_filteredType`, `nat_topologicalType` ->
	instance using `Pointed_isBaseTopological.Build`
  + filter now explicit in the notation `X --> Y`
    * lemmas `cvg_addnr`, `cvg_subnr`, `cvg_mulnl`, `cvg_mulnr`, `cvg_divnr`
  + definition `prod_topologicalTypeMixin`, canonical `prod_topologicalType` ->
    instances using `hasNbhs.Build`, `Nbhs_isNbhsTopological.Build`
  + definition `matrix_topologicalTypeMixin`, canonical `matrix_topologicalType` ->
    instance using `Nbhs_isNbhsTopological.Build`
  + definitions `weak_topologicalTypeMixin`, `weak_topologicalType` ->
    instances using `Pointed.on`, `Pointed_isOpenTopological.Build`
  + definitions `sup_topologicalTypeMixin`, `sup_topologicalType` ->
    instances using `Pointed.on` and `Pointed_isSubBaseTopological.Build`
  + definition `product_topologicalType` -> definition `product_topology_def`
    and instance using `Topological.copy`
  + in `lim_id`: `nbhs` now explicit
  + canonical `bool_discrete_topology` -> instance using `bool_discrete_topology`
  + module `Uniform` (packed class) -> mixin `Nbhs_isUniform_mixin`,
    structure `Uniform`, type `uniformType`,
    factories `Nbhs_isUniform`, `isUniform`
  + definition `prod_uniformType_mixin`, canonical `prod_uniformType` ->
    instance using `Nbhs_isUniform.Build`
  + definition `matrix_uniformType_mixin`, canonical `matrix_uniformType` ->
    instance using `Nbhs_isUniform.Build`
  + definitions `weak_uniform_mixin`, `weak_uniformType` -> instance
    using `Nbhs_isUniform.Build`
  + definitions `fct_uniformType_mixin`, `fct_topologicalTypeMixin`,
    `generic_source_filter`, `fct_topologicalType`, `fct_uniformType` ->
	definition `arrow_uniform` and instance using `arrow_uniform`
  + definitions `sup_uniform_mixin`, `sup_uniformType` -> instance using
    `Nbhs_isUniform.Build`
  + definition `product_uniformType` -> instance using `Uniform.copy`
  + definition `discrete_uniformType` -> instance using `Choice.on`,
    `Choice.on`, `discrete_uniform_mixin`
  + module `PseudoMetric` (packed class) -> factory `Nbhs_isPseudoMetric`
  + definition `ball` now a field of factory `Nbhs_isPseudoMetric`
  + definition `matrix_pseudoMetricType_mixin`, canonical `matrix_pseudoMetricType` ->
    instance using `Uniform_isPseudoMetric.Build`
  + definition `prod_pseudoMetricType_mixin`, canonical `prod_pseudoMetricType` ->
    instance using `Uniform_isPseudoMetric.Build`
  + definition `fct_pseudoMetricType_mixin`, canonical `fct_pseudoMetricType` ->
    instance using `Uniform_isPseudoMetric.Build`
  + canonical `quotient_subtype` -> instance using `Quotient.copy`
  + canonical `quotient_eq` -> instance using `[Sub ... of ... by %/]`
  + canonical `quotient_choice` -> instance using `[Choice of ... by <:]`
  + canonical `quotient_pointed` -> instance using `isPointed.Build`
  + in definition `quotient_topologicalType_mixin`:
    `topologyOfOpenMixin` -> `Pointed_isOpenTopological.Build`
  + canonical `quotient_topologicalType` -> instance using `quotient_topologicalType_mixin`
  + lemma `repr_comp_continuous` uses the notation `\pi_` instead of `... == ... %[mod ...]`
  + definition `discrete_pseudoMetricType` -> instead using `discrete_pseudometric_mixin`
  + module `Complete` (packed class) -> mixin `Uniform_isComplete`,
    structure `Complete`, type `completeType`
	  * lemma `cauchy_cvg` now a mixin field
  + canonical `matrix_completeType` -> instance using `Uniform_isComplete.Build`
  + canonical `fun_completeType` -> instance using `Uniform_isComplete.Build`
  + module `CompletePseudoMetric` (packed class) -> structure `CompletePseudoMetric`
  + matrix instance using `Uniform_isComplete.Build`
  + function instance using `Uniform_isComplete.Build`
  + module `regular_topology` -> instances using ` Pointed.on`,
    `hasNbhs.Build`, `Nbhs_isPseudoMetric.Build`
  + in module `numFieldTopology`:
    * `realType`, `rcfType`, `archiFieldType`, `realFieldType`, `numClosedFieldType`,
	  `numFieldType` instances using `PseudoMetric.copy`
  + definition `fct_RestrictedUniform`, `fct_RestrictedUniformTopology`, canonical
    `fct_RestrictUniformFilteredType`, `fct_RestrictUniformTopologicalType`, `fct_restrictedUniformType`
    ->
    definition `uniform_fun`, instance using `Unifom.copy` for ```{uniform` _ -> _}```
  + definitions `fct_Pointwise`, `fct_PointwiseTopology`, canonicals `fct_PointwiseFilteredType`,
    `fct_PointwiseTopologicalType` -> definition `pointwise_fun`, instance using `Topological.copy`
  + definition `compact_openK_topological_mixin`, canonical `compact_openK_filter`,
    `compact_openK_topological` -> instances using `Pointed.on`,
    `hasNbhs.Build`, `compact_openK_openE_subproof` for `compact_openK`
  + canonical `compact_open_pointedType`, definition `compact_open_topologicalType`,
    canonicals `compact_open_filtered`, `compact_open_filtered` -> definition `compact_open_def`,
	instances using `Pointed.on`, `Nbhs.copy`, `Pointed.on`, `Nbhs_isTopological`
  + definitions `weak_pseudoMetricType_mixin`, `weak_pseudoMetricType` -> lemmas
    `weak_pseudo_metric_ball_center`, `weak_pseudo_metric_entourageE`, instance using `niform_isPseudoMetric.Build`
  + definition `countable_uniform_pseudoMetricType_mixin` -> module `countable_uniform`
    with definition `type`, instances using `Uniform.on`, `Uniform_isPseudoMetric.Build`,
	lemma `countable_uniform_bounded`, notation `countable_uniform`
  + definitions `sup_pseudoMetric_mixin`, `sup_pseudoMetricType`, `product_pseudoMetricType` ->
    instances using `PseudoMetric.on`, `PseudoMetric.copy`
  + definitions `subspace_pointedType`, `subspace_topologicalMixin`, canonicals `subspace_filteredType`,
    `subspace_topologicalType` -> instance using `Choice.copy`, `isPointed.Build`, `hasNbhs.Build`,
	lemmas `nbhs_subspaceP_subproof`, `nbhs_subspace_singleton`, `nbhs_subspace_nbhs`, instance using
	`Nbhs_isNbhsTopological.Build`
  + definition `subspace_uniformMixin`, canonical `subspace_uniformType` -> instance using
    `Nbhs_isUniform_mixin.Build`
  + definition `subspace_pseudoMetricType_mixin`, canonical `subspace_pseudoMetricType` -> lemmas `subspace_pm_ball_center`,
    `subspace_pm_ball_sym`, `subspace_pm_ball_triangle`, `subspace_pm_entourageE`, instance using
    `Uniform_isPseudoMetric.Build`
  + section `gauges` -> module `gauge`
    * `gauge_pseudoMetricType` -> `gauge.type` (instances using `Uniform.on`, `PseudoMetric.on`)
	* `gauge_uniformType` -> `gauge.type`

### Renamed

### Generalized

- in `cantor.v`:
  + in definition `cantor_space`: `product_uniformType` -> `prod_topology`
	* instances using `Pointed.on`, `Nbhs.on`, `Topological.on`

- in `topology.v`:
  + now use `nbhsType` instead of `topologicalType`
    * lemma `near_fun`
    * definition `discrete_space`
    * definition `discrete_uniform_mixin`
	* definition `discrete_ball`, lemma `discrete_ball_center`,
	  definition `discrete_pseudometric_mixin`

### Deprecated

### Removed

- in `mathcomp_extra.v`:
  + coercion `choice.Choice.mixin`
  + lemmas `bigminr_maxr`, definitions `AC_subdef`, `oAC`, `opACE`, canonicals `opAC_law`, `opAC_com_law`
  + lemmas `some_big_AC`, `big_ACE`, `big_undup_AC`, `perm_big_AC`, `big_const_idem`,
    `big_id_idem`, `big_mkcond_idem`, `big_split_idem`, `big_id_idem_AC`, `bigID_idem`,
	`big_rem_AC`, `bigD1_AC`, `sub_big`, `sub_big_seq`, `sub_big_seq_cond`, `uniq_sub_big`,
	`uniq_sub_big_cond`, `sub_big_idem`, `sub_big_idem_cond`, `sub_in_big`, `le_big_ord`,
	`subset_big`, `subset_big_cond`, `le_big_nat`, `le_big_ord_cond`
  + lemmas `bigmax_le`, `bigmax_lt`, `lt_bigmin`, `le_bigmin`
  + lemmas `bigmax_mkcond`, `bigmax_split`, `bigmax_idl`, `bigmax_idr`, `bigmaxID`
  + lemmas `sub_bigmax`, `sub_bigmax_seq`, `sub_bigmax_cond`, `sub_in_bigmax`,
    `le_bigmax_nat`, `le_bigmax_nat_cond`, `le_bigmax_ord`, `le_bigmax_ord_cond`,
	`subset_bigmax`, `subset_bigmax_cond`
  + lemmas `bigmaxD1`, `le_bigmax_cond`, `le_bigmax`, `bigmax_sup`, `bigmax_leP`,
    `bigmax_ltP`, `bigmax_eq_arg`, `eq_bigmax`, `le_bigmax2`
  + lemmas `bigmin_mkcond`, `bigmin_split`, `bigmin_idl`, `bigmin_idr`, `bigminID`
  + lemmas `sub_bigmin`, `sub_bigmin_cond`, `sub_bigmin_seq`, `sub_in_bigmin`,
    `le_bigmin_nat`, `le_bigmin_nat_cond`, `le_bigmin_ord`, `le_bigmin_ord_cond`,
	`subset_bigmin`, `subset_bigmin_cond`
  + lemmas `bigminD1`, `bigmin_le_cond`, `bigmin_le`, `bigmin_inf`, `bigmin_geP`,
    `bigmin_gtP`, `bigmin_eq_arg`, `eq_bigmin`

- in `boolp.v`:
  + definitions `dep_arrow_eqType`, `dep_arrow_choiceClass`, `dep_arrow_choiceType`

- in `cardinality.v`:
  + lemma `countable_setT_countMixin`

- in `classical_sets.v`:
  + notations `PointedType`, `[pointedType of ...]`

- in `altreals/discrete.v`:
  + notation `[countable of ...]`

- in `cantor.v`:
  + definition `pointed_discrete`

- in `convex.v`:
  + field `convexspacechoiceclass`, canonicals `conv_eqType`, `conv_choiceType`, `conv_choiceType`

- in `constructive_ereal.v`:
  + canonicals `isLaw.Build`, `mine_comoid`

- in `lebesgue_measure.v`:
  + no more "pointed class" argument in definition `ereal_isMeasurable`

- in `measure.v`:
  + field `ptclass` in mixin `isSemiRingOfSets`
  + canonicals `ringOfSets_eqType`, `ringOfSets_choiceType`,
    `ringOfSets_ptType`, `algebraOfSets_eqType`, `algebraOfSets_choiceType`,
	`algebraOfSets_ptType`, `measurable_eqType`, `measurable_choiceType`,
	`measurable_ptType`
  + field `ptclass` in factory `isAlgebraOfSets`
  + field `ptclass` in factory `isMeasurable`

- in `normedtype.v`:
  + `filtered_of_normedZmod`
  + section `pseudoMetric_of_normedDomain`
    * lemmas `ball_norm_center`, `ball_norm_symmetric`, `ball_norm_triangle`, `nbhs_ball_normE`
	* definition `pseudoMetric_of_normedDomain`
  + lemma `normrZ`
  + canonical `matrix_normedZmodType`
  + lemmas `eq_cvg`, `eq_is_cvg`

- in `topology.v`:
  + structure `source`, definition `source_filter`
  + definition `filter_of`, notation `[filter of ...]` (now replaced by `nbhs`), lemma `filter_of_filterE`
  + definition `open_of_nbhs`
  + definition `open_from`, lemma `open_fromT`
  + canonical `eventually_filter_source`
  + canonical `discrete_topological_mixin`
  + canonical `set_filter_source`
  + definitions `filtered_of_normedZmod`, `pseudoMetric_of_normedDomain`
  + definitions `fct_UniformFamily` (use `uniform_fun_family` instead), canonicals `fct_UniformFamilyFilteredType`,
   `fct_UniformFamilyTopologicalType`, `fct_UniformFamilyUniformType`

- in `lebesgue_stieltjes_measure.v`
  + lemma `sigmaT_finite_lebesgue_stieltjes_measure` turned into a `Let`

### Infrastructure

### Misc
