# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
  + lemma `ball_subspace_ball`
- in `classical_sets.v`:
  + lemma `setCD`

- in `measure.v`:
  + factory `isAlgebraOfSets_setD`

- in `classical_sets.v`:
  + definition `setX`, notation ``` `^` ```
  + lemmas `setX0`, `set0X`, `setXK`, `setXC`, `setXA`, `setIXl`, `mulrXr`,
    `setX_def`, `setXE`, `setXU`, `setXI`, `setXD`, `setXCT`, `setCXT`, `setXTC`, `setTXC`
    
- in `measure.v`:
  + factory `isRingOfSets_setX`

- in `classical_sets.v`:
  + lemma `setDU`

- in `measure.v`:
  + definition `completed_measure_extension`
  + lemma `completed_measure_extension_sigma_finite`

- in `lebesgue_stieltjes_measure.v`:
  + definition `completed_lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + definition `completed_lebesgue_measure`
  + lemma `completed_lebesgue_measure_is_complete`
  + definition `completed_algebra_gen`
  + lemmas `g_sigma_completed_algebra_genE`, `negligible_sub_caratheodory`,
    `completed_caratheodory_measurable`
- in `ftc.v`:
  + lemma `FTC1` (specialization of the previous `FTC1` lemma, now renamed to `FTC1_lebesgue_pt`)
  + lemma `FTC1Ny`

- in `reals.v`:
  + lemma `mem_rg1_floor`

- in `mathcomp_extra.v`:
  + lemma `ge_floor`

- in `mathcomp_extra.v`:
  + lemmas `intr1D`, `intrD1`, `floor_eq`, `floorN`

- in `realfun.v`:
  + lemma `nondecreasing_at_left_is_cvgr`
- in `set_interval.v`:
  + lemmas `subset_itvl`, `subset_itvr`, `subset_itvS`

- in `normedtype.v`:
  + lemmas `nbhs_lt`, `nbhs_le`

- in `lebesgue_integral.v`:
  + lemmas `eq_Rintegral`, `Rintegral_mkcond`, `Rintegral_mkcondr`, `Rintegral_mkcondl`,
    `le_normr_integral`, `Rintegral_setU_EFin`, `Rintegral_set0`, `Rintegral_itv_bndo_bndc`,
    `Rintegral_itv_obnd_cbnd`, `Rintegral_set1`, `Rintegral_itvB`

- in `constructive_ereal.v`:
  + lemmas `lteD2rE`, `leeD2rE`
  + lemmas `lte_dD2rE`, `lee_dD2rE`

- in `mathcomp_extra.v`:
  + lemma `invf_ltp`

- in `classical_sets.v`:
  + lemmas `setC_I`, `bigcup_subset`

- in `set_interval.v`:
  + lemma `interval_set1`

- in `normedtype.v`:
  + lemma `nbhs_right_ltDr`

- in `numfun.v`:
  + lemma `epatch_indic`
  + lemma `restrict_normr`
  + lemmas `funepos_le`, `funeneg_le`

- in `ereal.v`:
  + lemmas `restrict_EFin`

- in `measure.v`:
  + definition `lim_sup_set`
  + lemmas `lim_sup_set_ub`, `lim_sup_set_cvg`, `lim_sup_set_cvg0`

- in `lebesgue_integral.v`:
  + lemma `integral_Sset1`
  + lemma `integralEpatch`
  + lemma `integrable_restrict`
  + lemma `le_integral`
  + lemma `null_set_integral`
  + lemma `EFin_normr_Rintegral`

- in `charge.v`:
  + definition `charge_variation`
  + lemmas `abse_charge_variation`, `charge_variation_continuous`
  + definition `induced`
  + lemmas `semi_sigma_additive_nng_induced`, `dominates_induced`, `integral_normr_continuous`

- in `ftc.v`:
  + definition `parameterized_integral`
  + lemmas `parameterized_integral_near_left`,
    `parameterized_integral_left`, `parameterized_integral_cvg_at_left`,
    `parameterized_integral_continuous`
  + corollary `continuous_FTC2`
- in `classical_sets.v`:
  + lemmas `xsectionP`, `ysectionP`

### Changed

- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in `lebesgue_integral.v`:
  + lemma `measurable_int`: argument `mu` now explicit 

- moved from `lebesgue_integral.v` to `ereal.v`:
  + lemma `funID`

- in `reals.v`:
  + definitions `Rceil`, `Rfloor`

- moved from `reals.v` to `mathcomp_extra.v`
  + lemma `lt_succ_floor`: conclusion changed to match `lt_succ_floor` in MathComp,
    generalized to `archiDomainType`
  + generalized to `archiDomainType`:
    lemmas `floor_ge0`, `floor_lt0`, `floor_natz`,
    `floor_ge_int`, `floor_neq0`, `floor_lt_int`, `ceil_ge`, `ceil_ge0`, `ceil_gt0`,
    `ceil_le0`, `ceil_ge_int`, `ceilN`, `abs_ceil_ge`
  + generalized to `archiDomainType` and precondition generalized:
    * `floor_le0`
  + generalized to `archiDomainType` and renamed:
    * `ceil_lt_int` -> `ceil_gt_int`

- moved from `lebesgue_integral.v` to `numfun.v`:
  + lemmas `fimfunEord`, `fset_set_comp`

- moved from `lebesgue_integral.v` to `cardinality.v`:
  + hint `solve [apply: fimfunP]`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pdivr_mull` -> `lte_pdivrMl`
  + `lte_pdivr_mulr` -> `lte_pdivrMr`
  + `lte_pdivl_mull` -> `lte_pdivlMl`
  + `lte_pdivl_mulr` -> `lte_pdivlMr`
  + `lte_ndivl_mulr` -> `lte_ndivlMr`
  + `lte_ndivl_mull` -> `lte_ndivlMl`
  + `lte_ndivr_mull` -> `lte_ndivrMl`
  + `lte_ndivr_mulr` -> `lte_ndivrMr`
  + `lee_pdivr_mull` -> `lee_pdivrMl`
  + `lee_pdivr_mulr` -> `lee_pdivrMr`
  + `lee_pdivl_mull` -> `lee_pdivlMl`
  + `lee_pdivl_mulr` -> `lee_pdivlMr`
  + `lee_ndivl_mulr` -> `lee_ndivlMr`
  + `lee_ndivl_mull` -> `lee_ndivlMl`
  + `lee_ndivr_mull` -> `lee_ndivrMl`
  + `lee_ndivr_mulr` -> `lee_ndivrMr`
  + `eqe_pdivr_mull` -> `eqe_pdivrMl`
- in `measure.v`:
  + `measurable_restrict` -> `measurable_restrictT`

- in `ftc.v`:
  + `FTC1` -> `FTC1_lebesgue_pt`
- in `measure.v`:
  + `setD_closed` -> `setSD_closed`

- in `constructive_ereal.v`:
  + `lte_dadd` -> `lte_dD`
  + `lee_daddl` -> `lee_dDl`
  + `lee_daddr` -> `lee_dDr`
  + `gee_daddl` -> `gee_dDl`
  + `gee_daddr` -> `gee_dDr`
  + `lte_daddl` -> `lte_dDl`
  + `lte_daddr` -> `lte_dDr`
  + `gte_dsubl` -> `gte_dBl`
  + `gte_dsubr` -> `gte_dBr`
  + `gte_daddl` -> `gte_dDl`
  + `gte_daddr` -> `gte_dDr`
  + `lee_dadd2lE` -> `lee_dD2lE`
  + `lte_dadd2lE` -> `lte_dD2lE`
  + `lee_dadd2rE` -> `lee_dD2rE`
  + `lee_dadd2l` -> `lee_dD2l`
  + `lee_dadd2r` -> `lee_dD2r`
  + `lee_dadd` -> `lee_dD`
  + `lee_dsub` -> `lee_dB`
  + `lte_dsubl_addr` -> `lte_dBlDr`
  + `lte_dsubl_addl` -> `lte_dBlDl`
  + `lte_dsubr_addr` -> `lte_dBrDr`
  + `lte_dsubr_addl` -> `lte_dBrDl`
  + `gte_opp` -> `gteN`
  + `gte_dopp` -> `gte_dN`
  + `lte_le_add` -> `lte_leD`
  + `lee_lt_add` -> `lee_ltD`
  + `lte_le_dadd` -> `lte_le_dD`
  + `lee_lt_dadd` -> `lee_lt_dD`
  + `lte_le_sub` -> `lte_leB`
  + `lte_le_dsub` -> `lte_le_dB`

- in `reals.v`:
  + `inf_lb` -> `inf_lbound`
  + `sup_ub` -> `sup_ubound`
  + `ereal_inf_lb` -> `ereal_inf_lbound`
  + `ereal_sup_ub` -> `ereal_sup_ubound`

### Generalized

- in `constructive_ereal.v`:
  + lemmas `leeN2`, `lteN2` generalized from `realDomainType` to `numDomainType`
- in `measure.v`:
  + lemma `measurable_restrict`

### Deprecated

- in `reals.v`:
  + `floor_le` (use `ge_floor` instead)
  + `le_floor` (use `Num.Theory.floor_le` instead)
  + `le_ceil` (use `ceil_ge` instead)
- in `lebesgue_integral.v`:
  + lemmas `integralEindic`, `integral_setI_indic`

- in `constructive_ereal.v`:
  + lemmas `lte_opp2`, `lee_opp2` (use `lteN2`, `leeN2` instead)

### Removed

- in `reals.v`:
  + definition `floor` (use `Num.floor` instead)
  + definition `ceil` (use `Num.ceil` instead)
  + lemmas `floor0`, `floor1`
  + lemma `le_floor` (use `Num.Theory.floor_le` instead)

- in `topology.v`, `function_spaces.v`, `normedtype.v`:
  + local notation `to_set`

### Infrastructure

### Misc
