# Changelog (unreleased)

## [Unreleased]

### Added

- in `mathcomp_extra.v`:
  + lemmas `prodr_ile1`, `nat_int`

- in `normedtype.v`:
  + lemma `scaler1`

- in `derive.v`:
  + lemmas `horner0_ext`, `hornerD_ext`, `horner_scale_ext`, `hornerC_ext`,
    `derivable_horner`, `derivE`, `continuous_horner`
  + instance `is_derive_poly`
- in file `separation_axioms.v`,
  + new lemmas `compact_normal_local`, and `compact_normal`.

- package `coq-mathcomp-experimental-reals` depending on `coq-mathcomp-reals`
  with files
  + `xfinmap.v`
  + `discrete.v`
  + `realseq.v`
  + `realsum.v`
  + `distr.v`

- package `coq-mathcomp-reals-stdlib` depending on `coq-mathcomp-reals`
  with file
  + `Rstruct.v`

- package `coq-mathcomp-analysis-stdlib` depending on
  `coq-mathcomp-analysis` and `coq-mathcomp-reals-stdlib` with files
  + `Rstruct_topology.v`
  + `showcase/uniform_bigO.v`

- in file `separation_axioms.v`,
  + new lemmas `compact_normal_local`, and `compact_normal`.

- in file `topology_theory/one_point_compactification.v`,
  + new definitions `one_point_compactification`, and `one_point_nbhs`.
  + new lemmas `one_point_compactification_compact`,
    `one_point_compactification_some_nbhs`,
    `one_point_compactification_some_continuous`,
    `one_point_compactification_open_some`,
    `one_point_compactification_weak_topology`, and
    `one_point_compactification_hausdorff`.

- in file `normedtype.v`,
  + new definition `type` (in module `completely_regular_uniformity`)
  + new lemmas `normal_completely_regular`,
    `one_point_compactification_completely_reg`,
    `nbhs_one_point_compactification_weakE`,
    `locally_compact_completely_regular`, and
    `completely_regular_regular`.
  + new lemmas `near_in_itvoy`, `near_in_itvNyo`

- in file `mathcomp_extra.v`,
  + new definition `sigT_fun`.
- in file `sigT_topology.v`,
  + new definition `sigT_nbhs`.
  + new lemmas `sigT_nbhsE`, `existT_continuous`, `existT_open_map`,
    `existT_nbhs`, `sigT_openP`, `sigT_continuous`, `sigT_setUE`, and 
    `sigT_compact`.
- in file `separation_axioms.v`,
  + new lemma `sigT_hausdorff`.

- in `measure.v`:
  + lemma `countable_measurable`
- in `realfun.v`:
  + lemma `cvgr_dnbhsP`
  + new definitions `prodA`, and `prodAr`.
  + new lemmas `prodAK`, `prodArK`, and `swapK`.
- in file `product_topology.v`,
  + new lemmas `swap_continuous`, `prodA_continuous`, and 
    `prodAr_continuous`.

- file `homotopy_theory/homotopy.v`
- file `homotopy_theory/wedge_sigT.v`
- in file `homotopy_theory/wedge_sigT.v`
  + new definitions `wedge_rel`, `wedge`, `wedge_lift`, `pwedge`.
  + new lemmas `wedge_lift_continuous`, `wedge_lift_nbhs`,
    `wedge_liftE`, `wedge_openP`,
    `wedge_pointE`, `wedge_point_nbhs`, `wedge_nbhs_specP`, `wedgeTE`,
    `wedge_compact`, `wedge_connected`.

- in `boolp.`:
  + lemma `existT_inj`
- in file `order_topology.v`
  + new lemmas `min_continuous`, `min_fun_continuous`, `max_continuous`, and
    `max_fun_continuous`.

- in file `bool_topology.v`,
  + new lemma `bool_compact`.

### Changed

- in file `normedtype.v`,
     changed `completely_regular_space` to depend on uniform separators
     which removes the dependency on `R`.  The old formulation can be
     recovered easily with `uniform_separatorP`.

- moved from `Rstruct.v` to `Rstruct_topology.v`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`,
    `continuity_ptE`, `continuity_pt_cvg'`, `continuity_pt_dnbhs`
    and `nbhs_pt_comp`

- moved from `real_interval.v` to `normedtype.v`
  + lemmas `set_itvK`, `RhullT`, `RhullK`, `set_itv_setT`,
    `Rhull_smallest`, `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`,
    `disj_itv_Rhull`
- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in `lebesgue_integral.v`:
  + lemmas `integral_fin_num_abs`, `Rintegral_cst`, `le_Rintegral`

- new file `pi_irrational.v`:
  + lemmas `measurable_poly`
  + definition `rational`
  + module `pi_irrational`
  + lemma `pi_irrationnal`

- in `numfun.v`
  + lemmas `funeposE`, `funenegE`, `funepos_comp`, `funeneg_comp`

- in `classical_sets.v`:
  + lemmas `xsectionE`, `ysectionE`

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`

- in `derive.v`:
  + put the notation ``` ^`() ``` and ``` ^`( _ ) ``` in scope `classical_set_scope`

- in `numfun.v`
  + lock `funepos`, `funeneg`

- moved from `lebesgue_integral.v` to `measure.v` and generalized
  + lemmas `measurable_xsection`, `measurable_ysection`
- moved from `topology_structure.v` to `discrete_topology.v`: 
  `discrete_open`, `discrete_set1`, `discrete_closed`, and `discrete_cvg`.

- moved from `pseudometric_structure.v` to `discrete_topology.v`:
    `discrete_ent`, `discrete_ball`, and `discrete_topology`.

- in file `cantor.v`, `cantor_space` now defined in terms of `bool`.
- in file `separation_axioms.v`, updated `discrete_hausdorff`, and
    `discrete_zero_dimension` to take a `discreteTopologicalType`.

### Renamed

- in `measure.v`
  + `preimage_class` -> `preimage_set_system`
  + `image_class` -> `image_set_system`
  + `preimage_classes` -> `g_sigma_preimageU`
  + `preimage_class_measurable_fun` -> `preimage_set_system_measurable_fun`
  + `sigma_algebra_preimage_class` -> `sigma_algebra_preimage`
  + `sigma_algebra_image_class` -> `sigma_algebra_image`
  + `sigma_algebra_preimage_classE` -> `g_sigma_preimageE`
  + `preimage_classes_comp` -> `g_sigma_preimageU_comp`

### Generalized

- in `sequences.v`,
  + generalized indexing from zero-based ones (`0 <= k < n` and `k <oo`)
    to `m <= k < n` and `m <= k <oo`
    * lemmas `nondecreasing_series`, `ereal_nondecreasing_series`,
             `eseries_mkcondl`, `eseries_mkcondr`, `eq_eseriesl`,
	     `nneseries_lim_ge`, `adde_def_nneseries`,
	     `nneseriesD`, `nneseries_sum_nat`, `nneseries_sum`,
  + lemmas `nneseries_ge0`, `is_cvg_nneseries_cond`, `is_cvg_npeseries_cond`,
    `is_cvg_nneseries`, `is_cvg_npeseries`, `nneseries_ge0`, `npeseries_le0`,
    `lee_nneseries`
    
### Deprecated

### Removed

- in `sequences.v`:
  + notations `nneseries_pred0`, `eq_nneseries`, `nneseries0`,
    `ereal_cvgPpinfty`, `ereal_cvgPninfty` (were deprecated since 0.6.0)
- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`

- in `cardinality.v`:
  + lemma `cst_fimfun_subproof`

- in `lebesgue_integral.v`:
  + lemma `cst_mfun_subproof` (use lemma `measurable_cst` instead)
  + lemma `cst_nnfun_subproof` (turned into a `Let`)
  + lemma `indic_mfun_subproof` (use lemma `measurable_fun_indic` instead)
- in file `topology_structure.v`, removed `discrete_sing`, `discrete_nbhs`, and `discrete_space`.
- in file `nat_topology.v`, removed `discrete_nat`.
- in file `pseudometric_structure.v`, removed `discrete_ball_center`, `discrete_topology_type`, and 
    `discrete_space_discrete`.

### Infrastructure

### Misc
