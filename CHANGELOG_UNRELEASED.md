# Changelog (unreleased)

## [Unreleased]

### Added

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)
  + lemmas `RabsE`, `RdistE`, `sum_f_R0E`, `factE`

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- file `constructive_ereal.v`:
  + definition `iter_mule`
  + lemma `prodEFin`

- file `exp.v`:
  + lemma `expR_sum`

- file `lebesgue_integral.v`:
  + lemma `measurable_fun_le`

- in `trigo.v`:
  + lemma `integral0oo_atan`

- in `measure.v`:
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`
  + lemma `preimage_set_system_id`

- in `Rstruct_topology.v`:
  + lemma `RexpE`

- in `derive.v`:
  + lemmas `derive_shift`, `is_derive_shift`

- in `interval_inference.v`:
  + definitions `IntItv.exprz`, `Instances.natmul_itv`
  + lemmas `Instances.num_spec_exprz`, `Instances.nat_spec_factorial`
  + canonical instance `Instances.exprz_inum`,
    `Instances.factorial_inum`

- in `mathcomp_extra.v`:
  + lemmas `exprz_ge0` and `exprz_gt0`

- in `exp.v`
  + lemmas `expR_le1`, `num_spec_expR`, `num_spec_powR`
  + definitions `expR_itv_boundl`, `expR_itv_boundr`, `expR_itv`,
    `powR_itv`
  + canonical instance `expR_inum`, `powR_inum`

- in `numfun.v`:
  + lemma `num_spec_indic`
  + canonical instance `indic_inum`

- in `trigo.v`:
  + lemmas `num_spec_sin`, `num_spec_cos`
  + canonical instances `sin_inum`, `cos_inum`

- in `mathcomp_extra.v`:
  + lemmas `intrN`, `real_floor_itv`, `real_ge_floor`, `real_ceil_itv`
- in `lebesgue_integral.v`:
  + lemma `dominated_cvg` (was previous `Local`)

- in `ftc.v`:
  + lemma `continuity_under_integral`

- in `set_interval.v`:
  + lemma `subset_itv`

- in `mathcomp_extra.v`:
  + lemmas `truncn_le`, `real_truncnS_gt`, `truncn_ge_nat`,
    `truncn_gt_nat`, `truncn_lt_nat`, `real_truncn_le_nat`,
    `truncn_eq`, `le_truncn`, `real_floorD1_gt`,
    `real_floor_ge_int_tmp`, `real_floor_ge_int`, `real_floor_lt_int`,
    `le_floor`, `real_floor_eq`, `real_floor_ge0`, `floor_lt0`,
    `real_floor_le0`, `floor_gt0`, `floor_neq0`,
    `real_ceil_le_int_tmp`, `real_ceil_le_int`, `real_ceil_gt_int`,
    `real_ceil_eq`, `le_ceil_tmp`, `real_ceil_ge0`, `ceil_lt0`,
    `real_ceil_le0`, `ceil_gt0`, `ceil_neq0`, `truncS_gt`,
    `truncn_le_nat`, `floorD1_gt`, `floor_ge_int_tmp`, `floor_lt_int`,
    `floor_eq`, `floor_ge0`, `floor_le0`, `ceil_le_int`,
    `ceil_le_int_tmp`, `ceil_gt_int`, `ceil_eq`, `ceil_ge0`,
    `ceil_le0`, `natr_int`

- new directory `lebesgue_integral_theory` with new files:
  + `simple_functions.v`
  + `lebesgue_integral_definition.v`
  + `lebesgue_integral_approximation.v`
  + `lebesgue_integral_monotone_convergence.v`
  + `lebesgue_integral_nonneg.v`
  + `lebesgue_integrable.v`
  + `lebesgue_integral_dominated_convergence.v`
  + `lebesgue_integral_under.v`
  + `lebesgue_Rintegral.v`
  + `lebesgue_integral_fubini.v`
  + `lebesgue_integral_differentiation.v`
  + `lebesgue_integral.v`

- in `sequences.v`:
  + lemmas `nneseriesD1`, `geometric_ge0`

- in `constructive_ereal.v`:
  + lemmas `EFin_fin_numP`, `EFin_bigmax`
- new directory `normedtype_theory` (that replaces `normedtype.v`) with new files:
  + `complete_normed_module.v`
  + `num_normedtype.v`
  + `ereal_normedtype.v`
  + `pseudometric_normed_Zmodule.v`
  + `matrix_normedtype.v`
  + `urysohn.v`
  + `normed_module.v`
  + `vitali_lemma.v`
  + `normedtype.v`

- in `realfun.v`:
  + lemmas `cvge_pinftyP`, `nonincreasing_cvge`

- in `probability.v`:
  + definition `cdf`
  + lemmas `cdf_ge0`, `cdf_le1`, `cdf_nondecreasing`, `cvg_cdfy1`, `cvg_cdfNy0`, `cdf_right_continuous`

- in `real_interval.v`:
  + lemma `itvNycEbigcap`
- in `normed_module.v` (new file):
  + lemma `near0Z`

- in `derive.v`:
  + lemma `near_eq_growth_rate`

- in `lebesgue_integral_theory/lebesgue_Rintegral.v`
  + lemma `RintegralD`
- in `numfun.v`:
  + lemmas `indicC`, `indic_bigcup`

- in `measure.v`:
  + lemmas `measurable_fun_pair1`, `measurable_fun_pair2`

- in `kernel.v`:
  + mixin `isSigmaFiniteTransitionKernel`, structure `SigmaFiniteTransitionKernel`,
    notations `sigma_finite_kernel`, `R .-sigmafker X ~> Y`
  + mixin `isFiniteTransition`, structure `FiniteTransitionKernel`,
    notations `finite_transition_kernel`, `R .-ftker X ~> Y`
  + lemmas `sprob_kernelP`, `sprob_kernel_le1`
  + definition `kfcomp`, lemmas `kfcompk1`, `kfcompkindic`, `measurable_kfcomp`
  + definitions `kproduct`, `kproduct_snd`
  + lemmas `measurable_kproduct`, `semi_sigma_additive_kproduct`
  + definition `mkproduct`
  + theorem `sigma_finite_mkproduct`
  + definition `kcomp_noparam`
  + lemma `kcomp_noparamE`
  + definition `mkcomp_noparam`
  + theorem `sprob_mkcomp_noparam`
- in `numfun.v`:
  + lemma `bounded_indic`

- in `lebesgue_integrable.v`:
  + lemma `integrable_indic_itv`

- in `probability.v`:
  + definitions `normal_fun`, `normal_peak`
  + lemmas `measurable_normal_fun`, `normal_fun_ge0`, `normal_fun_center`
  + lemmas `normal_peak_ge0`, `normal_peak_gt0`
  + lemma `normal_pdfE`
  + lemma `normal_pdf_ge0`, `normal_pdf_ub`
  + lemma `integrable_normal_pdf`

- in `derive.v`:
  + lemmas `derive1Mr`, `derive1Ml`
- in `derive.v`:
  + lemmas `ger0_derive1_le`, `ger0_derive1_le_cc`, `ger0_derive1_le_co`,
    `ger0_derive1_le_oc`, `ger0_derive1_le_oo`
  + lemmas `ler0_derive1_le`, `ler0_derive1_le_cc`, `ler0_derive1_le_co`,
    `ler0_derive1_le_oc`, `ler0_derive1_le_oo`
  + lemmas `ltr0_derive1_lt`, `ltr0_derive1_lt_cc`, `ltr0_derive1_lt_co`,
    `ltr0_derive1_lt_oc`, `ltr0_derive1_lt_oo`

### Changed

- file `separation_axioms.v` moved from `theories` to
  `theories/topology_theory`
- `topology.v` now exports `separation_axioms`

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package
- moved from `gauss_integral` to `trigo.v`:
  + `oneDsqr`, `oneDsqr_ge1`, `oneDsqr_inum`, `oneDsqrV_le1`,
    `continuous_oneDsqr`, `continuous_oneDsqr`
- moved, generalized, and renamed from `gauss_integral` to `trigo.v`:
  + `integral01_oneDsqr` -> `integral0_oneDsqr`

- in `interval_inference.v`:
  + definition `IntItv.exprn_le1_bound`
  + lemmas `Instances.nat_spec_succ`, `Instances.num_spec_natmul`,
    `Instances.num_spec_intmul`, `Instances.num_itv_bound_exprn_le1`
  + canonical instance `Instances.succn_inum`

- in `lebesgue_integral_properties.v`
  (new file with contents moved from `lebesgue_integral.v`)
  + `le_normr_integral` renamed to `le_normr_Rintegral`

- moved to `lebesgue_measure.v` (from old `lebesgue_integral.v`)
  + `compact_finite_measure`

- moved from `ftc.v` to `lebesgue_integral_under.v` (new file)
  + notation `'d1`, definition `partial1of2`, lemmas `partial1of2E`,
    `cvg_differentiation_under_integral`, `differentiation_under_integral`,
    `derivable_under_integral`

- in `classical_sets.v`:
  + change implicit arguments of `subsetT`
- moved from `normedtype.v` (old file) to `num_topology`
- moved from `normedtype.v` (old file) to `num_topology.v`
  + lemmas `nbhsN`, `cvg_compNP`, `nbhsNimage`, `nearN`, `openN`,
    `closedN`, `dnbhsN`, `closure_sup`, `right_bounded_interior`, `left_bounded_interior`,
    `withinN`

- the contents of `normedtype.v` (old file) can be found in the files in directory
  `normed_theory` unless stated otherwise

- in `filter.v`:
  + change implicit arguments of `cvg_comp`

- in `probability.v`:
  + definition `normal_pdf` changed to use `normal_fun` and `normal_peak`

### Renamed

- in `lebesgue_integral.v`:
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`
  + `measurable_funP` -> `measurable_funPT` (field of `isMeasurableFun` mixin)

- in `mathcomp_extra.v`
  + `comparable_min_le_min` -> `comparable_le_min2`
  + `comparable_max_le_max` -> `comparable_le_max2`
  + `min_le_min` -> `le_min2`
  + `max_le_max` -> `le_max2`
  + `real_sqrtC` -> `sqrtC_real`

- in `boolp.v`:
  + `eq_fun2` -> `eq2_fun`
  + `eq_fun3` -> `eq3_fun`
  + `eq_forall2` -> `eq2_forall`
  + `eq_forall3` -> `eq3_forall`
- in `real_interval.v`:
  + `itv_c_inftyEbigcap` -> `itvcyEbigcap`
  + `itv_bnd_inftyEbigcup` -> `itvbndyEbigcup`
  + `itv_o_inftyEbigcup` -> `itvoyEbigcup`

- in `measure.v`:
  + `measurable_fun_prod` -> `measurable_fun_pair`
  + `prod_measurable_funP` -> `measurable_fun_pairP`
  + `measurable_pair1` -> `pair1_measurable`
  + `measurable_pair2` -> `pair2_measurable`

- in `kernel.v`:
  + `Kernel_isSFinite_subdef` -> `isSFiniteKernel_subdef`
  + `SFiniteKernel_isFinite` -> `isMeasureFamUub`
  + `FiniteKernel_isSubProbability` -> `isSubProbabilityKernel`
  + `SubProbability_isProbability` -> `isProbabilityKernel`
- in `set_interval.v`:
  + `set_itv_infty_infty` -> `set_itvNyy`
  + `set_itv_o_infty` -> `set_itvoy`
  + `set_itv_c_infty` -> `set_itvcy`
  + `set_itv_infty_o` -> `set_itvNyo`
  + `set_itv_infty_c` -> `set_itvNyc`
  + `set_itv_pinfty_bnd` -> `set_itv_ybnd`
  + `set_itv_bnd_ninfty` -> `set_itv_bndNy`

- in `normed_module.v` (new file):
  + `cvgeMl` -> `cvgeZl`
  + `is_cvgeMl` -> `is_cvgeZl`
  + `cvgeMr` -> `cvgeZr`
  + `is_cvgeMr` -> `is_cvgeZr`

### Generalized

- in `constructive_ereal.v`:
  + lemma `EFin_natmul`

- in `lebesgue_integral.v`
  + lemmas `measurable_funP`, `ge0_integral_pushforward`,
    `integrable_pushforward`, `integral_pushforward`

- in `real_interval.v`:
  + lemmas `bigcup_itvT`, `itv_bndy_bigcup_BRight`, `itv_bndy_bigcup_BLeft_shift`

- in `sequences.v`:
  + lemma `nneseries_recl` genralized with a filtering predicate `P`
- in `normedtype.v`:
- in `ereal_normedtype.v` (new file, was `normedtype.v`):
  + `lower_semicontinuous`, `lower_semicontinuousP` generalized from `realType` to `numFieldType`

- in `num_normedtype.v` (new file):
  + lemmas `gt0_cvgMlNy`, `gt0_cvgMly`
- in `pseudometric_normed_Zmodule.v`:
  + generalized from `normedModType` to `pseudoMetricNormedZmodType`:
    * lemmas `cvgr_norm_lty`, `cvgr_norm_ley`, `cvgr_norm_gtNy`,
      `cvgr_norm_geNy`, `cvg_bounded`

### Deprecated

- in `normed_theory` (was in `normedtype.v` before the split)
  + `pseudoMetricNormedZModType_hausdorff` (use `norm_hausdorff` instead)
- in `derive.v`:
  + `ler0_derive1_nincr` (use `ler0_derive1_le_cc`)
  + `gtr0_derive1_incr` (use `gtr0_le_derive1`)

### Removed

- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)
  + lemma `deg_le2_ge0` (available as `deg_le2_poly_ge0` in `ssrnum.v`
    since MathComp 2.1.0)
  + definitions `monotonous`, `boxed`, `onem`, `inv_fun`,
    `bound_side`, `swap`, `prodA`, `prodAr`, `map_pair`, `sigT_fun`
    (moved to new file `unstable.v` that shouldn't be used outside of
    Analysis)
  + notations `` `1 - r ``, `f \^-1` (moved to new file `unstable.v`
    that shouldn't be used outside of Analysis)
  + lemmas `dependent_choice_Type`, `maxr_absE`, `minr_absE`,
    `le_bigmax_seq`, `bigmax_sup_seq`, `leq_ltn_expn`, `last_filterP`,
    `path_lt_filter0`, `path_lt_filterT`, `path_lt_head`,
    `path_lt_last_filter`, `path_lt_le_last`, `sumr_le0`,
    `fset_nat_maximum`, `image_nat_maximum`, `card_fset_sum1`,
    `onem0`, `onem1`, `onemK`, `add_onemK`, `onem_gt0`, `onem_ge0`,
    `onem_le1`, `onem_lt1`, `onemX_ge0`, `onemX_lt1`, `onemD`,
    `onemMr`, `onemM`, `onemV`, `lez_abs2`, `ler_gtP`, `ler_ltP`,
    `real_ltr_distlC`, `prodAK`, `prodArK`, `swapK`, `lt_min_lt`,
    `intrD1`, `intr1D`, `floor_lt_int`, `floor_ge0`, `floor_le0`,
    `floor_lt0`, `floor_eq`, `floor_neq0`, `ceil_gt_int`, `ceil_ge0`,
    `ceil_gt0`, `ceil_le0`, `abs_ceil_ge`, `nat_int`, `bij_forall`,
    `and_prop_in`, `mem_inc_segment`, `mem_dec_segment`,
    `partition_disjoint_bigfcup`, `partition_disjoint_bigfcup`,
    `prodr_ile1`, `size_filter_gt0`, `ltr_sum`, `ltr_sum_nat` (moved
    to new file `unstable.v` that shouldn't be used outside of
    Analysis)

- in `reals.v`:
  + lemmas `floor_le`, `le_floor` (deprecated since 1.3.0)

- file `lebesgue_integral.v` (split in several files in the directory
  `lebesgue_integral_theory`)

- in `classical_sets.v`:
  + notations `setvI`, `setIv`, `bigcup_set`, `bigcup_set_cond`, `bigcap_set`,
    `bigcap_set_cond`

- in `measure.v`:
  + notations `measurable_fun_fst`, `measurable_fun_snd`, `measurable_fun_swap`
    (deprecated since 0.6.3)

- in `filter.v`:
  + definition `at_point` (redundant with `principal_filter`)
- file `normedtype.v` (split in several files in the directory
  `normed_theory`)

### Infrastructure

### Misc
