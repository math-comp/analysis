# Changelog

Last releases: [[0.3.4] - 2020-12-12](#034---2020-12-12) and [[0.3.3] - 2020-11-11](#033---2020-11-11)

## [0.3.4] - 2020-12-12

### Added

- in `classical_sets.v`:
  + lemma `bigcup_distrl`
  + definition `trivIset`
  + lemmas `trivIset_bigUI`, `trivIset_setI`
- in `ereal.v`:
  + definition `mule` and its notation `*` (scope `ereal_scope`)
  + definition `abse` and its notation `` `| | `` (scope `ereal_scope`)
- in `normedtype.v`:
  + lemmas `closure_sup`, `near_infty_natSinv_lt`, `limit_pointP`
  + lemmas `closure_gt`, `closure_lt`
  + definition `is_interval`, `is_intervalPle`, `interval_is_interval`
  + lemma `connected_intervalP`
  + lemmas `interval_open` and `interval_closed`
  + lemmas `inf_lb_strict`, `sup_ub_strict`, `interval_unbounded_setT`,
    `right_bounded_interior`, `interval_left_unbounded_interior`, `left_bounded_interior`,
    `interval_right_unbounded_interior`, `interval_bounded_interior`
  + definition `Rhull`
  + lemma `sub_Rhull`, `is_intervalP`
- in `measure.v`:
  + definition `bigcup2`, lemma `bigcup2E`
  + definitions `isSemiRingOfSets`, `SemiRingOfSets`, notation `semiRingOfSetsType`
  + definitions `RingOfSets_from_semiRingOfSets`, `RingOfSets`, notation `ringOfSetsType`
  + factory: `isRingOfSets`
  + definitions `Measurable_from_ringOfSets`, `Measurable`
  + lemma `semiRingOfSets_measurable{I,D}`
  + definition `diff_fsets`, lemmas `semiRingOfSets_diff_fsetsE`, `semiRingOfSets_diff_fsets_disjoint`
  + definitions `isMeasurable`
  + factory: `isMeasurable`
  + lemma `bigsetU_measurable`, `measurable_bigcap`
  + definitions `semi_additive2`, `semi_additive`, `semi_sigma_additive`
  + lemmas `semi_additive2P`, `semi_additiveE`, `semi_additive2E`,
    `semi_sigma_additive_is_additive`, `semi_sigma_additiveE`
  + `Module AdditiveMeasure`
     * notations `additive_measure`, `{additive_measure set T -> {ereal R}}`
  + lemmas `measure_semi_additive2`, `measure_semi_additive`, `measure_semi_sigma_additive`
  + lemma `semi_sigma_additive_is_additive`, canonical/coercion `measure_additive_measure`
  + lemma `sigma_additive_is_additive`
  + notations `ringOfSetsType`, `outer_measure`
  + definition `negligible` and its notation `.-negligible`
  + lemmas `negligibleP`, `negligible_set0`
  + definition `almost_everywhere` and its notation `{ae mu, P}`
  + lemma `satisfied_almost_everywhere`
  + definition `sigma_subadditive`
  + `Module OuterMeasure`
    * notation `outer_measure`, `{outer_measure set T -> {ereal R}}`
  + lemmas `outer_measure0`, `outer_measure_ge0`, `le_outer_measure`,
    `outer_measure_sigma_subadditive`, `le_outer_measureIC`
- in `boolp.v`:
  + lemmas `and3_asboolP`, `or3_asboolP`, `not_and3P`
- in `classical_sets.v`:
  + lemma `bigcup_sup`
- in `topology.v`:
  + lemmas `closure0`, `separatedC`, `separated_disjoint`, `connectedP`, `connected_subset`,
    `bigcup_connected`
  + definition `connected_component`
  + lemma `component_connected`

### Changed

- in `ereal.v`:
  + notation `x >= y` defined as `y <= x` (only parsing) instead of `gee`
  + notation `x > y` defined as `y < x` (only parsing) instead of `gte`
  + definition `mkset`
  + lemma `eq_set`
- in `classical_sets.v`:
  + notation `[set x : T | P]` now use definition `mkset`
- in `reals.v`:
  + lemmas generalized from `realType` to `numDomainType`:
    `setNK`, `memNE`, `lb_ubN`, `ub_lbN`, `nonemptyN`, `has_lb_ubN `
  + lemmas generalized from `realType` to `realDomainType`:
    `has_ubPn`, `has_lbPn`

## Renamed

- in `classical_sets.v`:
  + `subset_empty` -> `subset_nonempty`
- in `measure.v`:
  + `sigma_additive_implies_additive` -> `sigma_additive_is_additive`
- in `topology.v`:
  + `nbhs_of` -> `locally_of`
- in `topology.v`:
  + `connect0` -> `connected0`

## [0.3.3] - 2020-11-11

### Added

- in `boolp.v`:
  + lemma `not_andP`
  + lemma `not_exists2P`
- in `classical_sets.v`:
  + lemmas `setIIl`, `setIIr`, `setCS`, `setSD`, `setDS`, `setDSS`, `setCI`,
    `setDUr`, `setDUl`, `setIDA`, `setDD`
  + definition `dep_arrow_choiceType`
  + lemma `bigcup_set0`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`, `subsetEset`, `subEset`, `complEset`, `botEset`, `topEset`, `meetEset`, `joinEset`, `subsetPset`, `properPset`
  + Canonical `porderType`, `latticeType`, `distrLatticeType`, `blatticeType`, `tblatticeType`, `bDistrLatticeType`, `tbDistrLatticeType`, `cbDistrLatticeType`, `ctbDistrLatticeType`
  + lemmas `set0M`, `setM0`, `image_set0_set0`, `subset_set1`, `preimage_set0`
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
  + new lemmas: `lb_set1`, `ub_lb_set1`, `ub_lb_refl`, `lb_ub_lb`
  + new definitions and lemmas: `infimums`, `infimum`, `infimums_set1`, `is_subset1_infimum`
  + new lemmas: `ge_supremum_Nmem`, `le_infimum_Nmem`, `nat_supremums_neq0`
  + lemmas `setUCl`, `setDv`
  + lemmas `image_preimage_subset`, `image_subset`, `preimage_subset`
  + definition `proper` and its notation `<`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`
  + lemmas `setUK`, `setKU`, `setIK`, `setKI`, `subsetEset`, `subEset`, `complEset`, `botEset`, `topEset`, `meetEset`, `joinEset`, `properEneq`
  + Canonical `porderType`, `latticeType`, `distrLatticeType`, `blatticeType`, `tblatticeType`, `bDistrLatticeType`, `tbDistrLatticeType`, `cbDistrLatticeType`, `ctbDistrLatticeType` on classical `set`.
- file `nngnum.v`
- in `topology.v`:
  + definition `meets` and its notation `#`
  + lemmas `meetsC`, `meets_openr`, `meets_openl`, `meets_globallyl`,
    `meets_globallyr `, `meetsxx` and `proper_meetsxx`.
  + definition `limit_point`
  + lemmas `subset_limit_point`, `closure_limit_point`,
    `closure_subset`, `closureE`, `closureC`, `closure_id`
  + lemmas `cluster_nbhs`, `clusterEonbhs`, `closureEcluster`
  + definition `separated`
  + lemmas `connected0`, `connectedPn`, `connected_continuous_connected`
  + lemmas `closureEnbhs`, `closureEonbhs`, `limit_pointEnbhs`,
    `limit_pointEonbhs`, `closeEnbhs`, `closeEonbhs`.
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`
  + lemmas `gee0P`, `sume_ge0`, `lee_sum_nneg`, `lee_sum_nneg_ord`, `lee_sum_nneg_subset`, `lee_sum_nneg_subfset`
  + lemma `lee_addr`
  + lemma `lee_adde`
  + lemma `oppe_continuous`
  + lemmas `ereal_nbhs_pinfty_ge`, `ereal_nbhs_ninfty_le`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`, `geometric_invn`
  + lemmas `increasing_series`, `cvg_shiftS`, `mulrn_arithmetic`,
    `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`,
    `is_cvg_geometric_series`.
  + lemmas `ereal_cvgN`, `ereal_cvg_ge0`, `ereal_lim_ge`, `ereal_lim_le`
  + lemma `ereal_cvg_real`
  + lemmas `is_cvg_ereal_nneg_series_cond`, `is_cvg_ereal_nneg_series`, `ereal_nneg_series_lim_ge0`,
    `ereal_nneg_series_pinfty`
  + lemmas `ereal_cvgPpinfty`, `ereal_cvgPninfty`, `lee_lim`
  + lemma `ereal_cvgD`
    * with intermediate lemmas `ereal_cvgD_pinfty_fin`, `ereal_cvgD_ninfty_fin`, `ereal_cvgD_pinfty_pinfty`,
      `ereal_cvgD_ninfty_ninfty`
  + lemma `ereal_limD`
- in `normedtype.v`:
  + lemma `closed_ereal_le_ereal`
  + lemma `closed_ereal_ge_ereal`
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`

### Changed

- in `classical_sets.v`:
  + the index in `bigcup_set1` generalized from `nat` to some `Type`
  + lemma `bigcapCU` generalized
  + lemmas `preimage_setU` and `preimage_setI` are about the `setU` and `setI` (instead of `bigcup` and `bigcap`)
  + `eqEsubset` changed from an implication to an equality
- lemma `asboolb` moved from `discrete.v` to `boolp.v`
- lemma `exists2NP` moved from `discrete.v` to `boolp.v`
- lemma `neg_or` moved from `discrete.v` to `boolp.v` and renamed to `not_orP`
- definitions `dep_arrow_choiceClass` and `dep_arrow_pointedType`
  slightly generalized and moved from `topology.v` to
  `classical_sets.v`
- the types of the topological notions for `numFieldType` have been moved from `normedtype.v` to `topology.v`
- the topology of extended real numbers has been moved from `normedtype.v` to `ereal.v` (including the notions of filters)
- `numdFieldType_lalgType` in `normedtype.v` renamed to `numFieldType_lalgType` in `topology.v`
- in `ereal.v`:
  + the first argument of `real_of_er` is now maximal implicit
  + the first argument of `is_real` is now maximal implicit
  + generalization of `lee_sum`
- in `boolp.v`:
  + rename `exists2NP` to `forall2NP` and make it bidirectionnal
- moved the definition of `{nngnum _}` and the related bigmax theory to the new `nngnum.v` file

### Renamed

- in `classical_sets.v`:
  + `setIDl` -> `setIUl`
  + `setUDl` -> `setUIl`
  + `setUDr` -> `setUIr`
  + `setIDr` -> `setIUl`
  + `setCE` -> `setTD`
  + `preimage_setU` -> `preimage_bigcup`, `preimage_setI` -> `preimage_bigcap`
- in `boolp.v`:
  + `contrap` -> `contra_not`
  + `contrapL` -> `contraPnot`
  + `contrapR` -> `contra_notP`
  + `contrapLR` -> `contraPP`

### Removed

- in `boolp.v`:
  + `contrapNN`, `contrapTN`, `contrapNT`, `contrapTT`
  + `eqNN`
- in `normedtype.v`:
  + `forallN`
  + `eqNNP`
  + `existsN`
- in `discrete.v`:
  + `existsP`
  + `existsNP`
- in `topology.v`:
  + `close_to`
  + `close_cluster`, which is subsumed by `closeEnbhs`

## [0.3.2] - 2020-08-11

### Added

- in `boolp.v`, new lemma `andC`
- in `topology.v`:
  + new lemma `open_nbhsE`
  + `uniformType` a structure for uniform spaces based on entourages
    (`entourage`)
  + `uniformType` structure on products, matrices, function spaces
  + definitions `nbhs_`, `topologyOfEntourageMixin`, `split_ent`, `nbhsP`,
    `entourage_set`, `entourage_`, `uniformityOfBallMixin`, `nbhs_ball`
  + lemmas `nbhs_E`, `nbhs_entourageE`, `filter_from_entourageE`,
    `entourage_refl`, `entourage_filter`, `entourageT`, `entourage_inv`,
    `entourage_split_ex`, `split_entP`, `entourage_split_ent`,
    `subset_split_ent`, `entourage_split`, `nbhs_entourage`, `cvg_entourageP`,
    `cvg_entourage`, `cvg_app_entourageP`, `cvg_mx_entourageP`,
    `cvg_fct_entourageP`, `entourage_E`, `entourage_ballE`,
    `entourage_from_ballE`, `entourage_ball`, `entourage_proper_filter`,
    `open_nbhs_entourage`, `entourage_close`
  + `completePseudoMetricType` structure
  + `completePseudoMetricType` structure on matrices and function spaces
- in `classical_sets.v`:
  + lemmas `setICr`, `setUidPl`, `subsets_disjoint`, `disjoints_subset`, `setDidPl`,
    `setIidPl`, `setIS`, `setSI`, `setISS`, `bigcup_recl`, `bigcup_distrr`,
    `setMT`
- in `ereal.v`:
  + notation `\+` (`ereal_scope`) for function addition
  + notations `>` and `>=` for comparison of extended real numbers
  + definition `is_real`, lemmas `is_realN`, `is_realD`, `ERFin_real_of_er`, `adde_undef`
  + basic lemmas: `addooe`, `adde_Neq_pinfty`, `adde_Neq_ninfty`, `addERFin`,
    `subERFin`, `real_of_erN`, `lb_ereal_inf_adherent`
  + arithmetic lemmas: `oppeD`, `subre_ge0`, `suber_ge0`, `lee_add2lE`, `lte_add2lE`,
    `lte_add`, `lte_addl`, `lte_le_add`, `lte_subl_addl`, `lee_subr_addr`,
    `lee_subl_addr`, `lte_spaddr`, `addeAC`, `addeCA`
- in `normedtype.v`:
  + lemmas `natmul_continuous`, `cvgMn` and `is_cvgMn`.
  + `uniformType` structure for `ereal`
- in `sequences.v`:
  + definitions `arithmetic`, `geometric`
  + lemmas `telescopeK`, `seriesK`, `increasing_series`, `cvg_shiftS`,
     `mulrn_arithmetic`, `exprn_geometric`, `cvg_arithmetic`, `cvg_expr`,
    `geometric_seriesE`, `cvg_geometric_series`, `is_cvg_geometric_series`.

### Changed

- moved from `normedtype.v` to `boolp.v` and renamed:
  + `forallN` -> `forallNE`
  + `existsN` -> `existsNE`
- `topology.v`:
  + `unif_continuous` uses `entourage`
  + `pseudoMetricType` inherits from `uniformType`
  + `generic_source_filter` and `set_filter_source` use entourages
  + `cauchy` is based on entourages and its former version is renamed
    `cauchy_ball`
  + `completeType` inherits from `uniformType` and not from `pseudoMetricType`
- moved from `posnum.v` to `Rbar.v`: notation `posreal`
- moved from `normedtype.v` to `Rstruct.v`:
  + definitions `R_pointedType`, `R_filteredType`, `R_topologicalType`,
    `R_uniformType`, `R_pseudoMetricType`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`, `continuity_ptE`,
    `continuity_pt_cvg'`, `continuity_pt_nbhs'`, `nbhs_pt_comp`
  + lemmas `close_trans`, `close_cvgxx`, `cvg_closeP` and `close_cluster` are
    valid for a `uniformType`
  + moved `continuous_withinNx` from `normedType.v` to `topology.v` and
    generalised it to `uniformType`
- moved from `measure.v` to `sequences.v`
  + `ereal_nondecreasing_series`
  + `ereal_nneg_series_lim_ge` (renamed from `series_nneg`)

### Renamed

- in `classical_sets.v`,
  + `ub` and `lb` are renamed to `ubound` and `lbound`
  + new lemmas:
    * `setUCr`, `setCE`, `bigcup_set1`, `bigcapCU`, `subset_bigsetU`
- in `boolp.v`,
  + `existsPN` -> `not_existsP`
  + `forallPN` -> `not_forallP`
  + `Nimply` -> `not_implyP`
- in `classical_sets.v`, `ub` and `lb` are renamed to `ubound` and `lbound`
- in `ereal.v`:
  + `eadd` -> `adde`, `eopp` -> `oppe`
- in `topology.v`:
  + `locally` -> `nbhs`
  + `locally_filterE` -> `nbhs_filterE`
  + `locally_nearE` -> `nbhs_nearE`
  + `Module Export LocallyFilter` -> `Module Export NbhsFilter`
  + `locally_simpl` -> `nbhs_simpl`
    * three occurrences
  + `near_locally` -> `near_nbhs`
  + `Module Export NearLocally` -> `Module Export NearNbhs`
  + `locally_filter_onE` -> `nbhs_filter_onE`
  + `filter_locallyT` -> `filter_nbhsT`
  + `Global Instance locally_filter` -> `Global Instance nbhs_filter`
  + `Canonical locally_filter_on` -> `Canonical nbhs_filter_on`
  + `neigh` -> `open_nbhs`
  + `locallyE` -> `nbhsE`
  + `locally_singleton` -> `nbhs_singleton`
  + `locally_interior` -> `nbhs_interior`
  + `neighT` -> `open_nbhsT`
  + `neighI` -> `open_nbhsI`
  + `neigh_locally` -> `open_nbhs_nbhs`
  + `within_locallyW` -> `within_nbhsW`
  + `prod_loc_filter` -> `prod_nbhs_filter`
  + `prod_loc_singleton` -> `prod_nbhs_singleton`
  + `prod_loc_loc` -> `prod_nbhs_nbhs`
  + `mx_loc_filter` -> `mx_nbhs_filter`
  + `mx_loc_singleton` -> `mx_nbhs_singleton`
  + `mx_loc_loc` -> `mx_nbhs_nbhs`
  + `locally'` -> `nbhs'`
  + `locallyE'` -> `nbhsE'`
  + `Global Instance locally'_filter` -> `Global Instance nbhs'_filter`
  + `Canonical locally'_filter_on` -> `Canonical nbhs'_filter_on`
  + `locally_locally'` -> `nbhs_nbhs'`
  + `Global Instance within_locally_proper` -> `Global Instance within_nbhs_proper`
  + `locallyP` -> `nbhs_ballP`
  + `locally_ball` -> `nbhsx_ballx`
  + `neigh_ball` -> `open_nbhs_ball`
  + `mx_locally` -> `mx_nbhs`
  + `prod_locally` -> `prod_nbhs`
  + `Filtered.locally_op` -> `Filtered.nbhs_op`
  + `locally_of` -> `nbhs_of`
  + `open_of_locally` -> `open_of_nhbs`
  + `locally_of_open` -> `nbhs_of_open`
  + `locally_` -> `nbhs_ball`
  + lemma `locally_ballE` -> `nbhs_ballE`
  + `locallyW` -> `nearW`
  + `nearW` -> `near_skip_subproof`
  + `locally_infty_gt` -> `nbhs_infty_gt`
  + `locally_infty_ge` -> `nbhs_infty_ge`
  + `cauchy_entouragesP` -> `cauchy_ballP`
- in `normedtype.v`:
  + `locallyN` -> `nbhsN`
  + `locallyC` -> `nbhsC`
  + `locallyC_ball` -> `nbhsC_ball`
  + `locally_ex` -> `nbhs_ex`
  + `Global Instance Proper_locally'_numFieldType` -> `Global Instance Proper_nbhs'_numFieldType`
  + `Global Instance Proper_locally'_realType` -> `Global Instance Proper_nbhs'_realType`
  + `ereal_locally'` -> `ereal_nbhs'`
  + `ereal_locally` -> `ereal_nbhs`
  + `Global Instance ereal_locally'_filter` -> `Global Instance ereal_nbhs'_filter`
  + `Global Instance ereal_locally_filter` -> `Global Instance ereal_nbhs_filter`
  + `ereal_loc_singleton` -> `ereal_nbhs_singleton`
  + `ereal_loc_loc` -> `ereal_nbhs_nbhs`
  + `locallyNe` -> `nbhsNe`
  + `locallyNKe` -> `nbhsNKe`
  + `locally_oo_up_e1` -> `nbhs_oo_up_e1`
  + `locally_oo_down_e1` -> `nbhs_oo_down_e1`
  + `locally_oo_up_1e` -> `nbhs_oo_up_1e`
  + `locally_oo_down_1e` -> `nbhs_oo_down_1e`
  + `locally_fin_out_above` -> `nbhs_fin_out_above`
  + `locally_fin_out_below` -> `nbhs_fin_out_below`
  + `locally_fin_out_above_below` -> `nbhs_fin_out_above_below`
  + `locally_fin_inbound` -> `nbhs_fin_inbound`
  + `ereal_locallyE` -> `ereal_nbhsE`
  + `locally_le_locally_norm` -> `nbhs_le_locally_norm`
  + `locally_norm_le_locally` -> `locally_norm_le_nbhs`
  + `locally_locally_norm` -> `nbhs_locally_norm`
  + `filter_from_norm_locally` -> `filter_from_norm_nbhs`
  + `locally_ball_norm` -> `nbhs_ball_norm`
  + `locally_simpl` -> `nbhs_simpl`
  + `Global Instance filter_locally` -> `Global Instance filter_locally`
  + `locally_interval` -> `nbhs_interval`
  + `ereal_locally'_le` -> `ereal_nbhs'_le`
  + `ereal_locally'_le_finite` -> `ereal_nbhs'_le_finite`
  + `locally_image_ERFin` -> `nbhs_image_ERFin`
  + `locally_open_ereal_lt` -> `nbhs_open_ereal_lt`
  + `locally_open_ereal_gt` -> `nbhs_open_ereal_gt`
  + `locally_open_ereal_pinfty` -> `nbhs_open_ereal_pinfty`
  + `locally_open_ereal_ninfty` -> `nbhs_open_ereal_ninfty`
  + `continuity_pt_locally` -> `continuity_pt_nbhs`
  + `continuity_pt_locally'` -> `continuity_pt_nbhs'`
  + `nbhs_le_locally_norm` -> `nbhs_le_nbhs_norm`
  + `locally_norm_le_nbhs` -> `nbhs_norm_le_nbhs`
  + `nbhs_locally_norm` -> `nbhs_nbhs_norm`
  + `locally_normP` -> `nbhs_normP`
  + `locally_normE` -> `nbhs_normE`
  + `near_locally_norm` -> `near_nbhs_norm`
  + lemma `locally_norm_ball_norm` -> `nbhs_norm_ball_norm`
  + `locally_norm_ball` -> `nbhs_norm_ball`
  + `pinfty_locally` -> `pinfty_nbhs`
  + `ninfty_locally` -> `ninfty_nbhs`
  + lemma `locally_pinfty_gt` -> `nbhs_pinfty_gt`
  + lemma `locally_pinfty_ge` -> `nbhs_pinfty_ge`
  + lemma `locally_pinfty_gt_real` -> `nbhs_pinfty_gt_real`
  + lemma `locally_pinfty_ge_real` -> `nbhs_pinfty_ge_real`
  + `locally_minfty_lt` -> `nbhs_minfty_lt`
  + `locally_minfty_le` -> `nbhs_minfty_le`
  + `locally_minfty_lt_real` -> `nbhs_minfty_lt_real`
  + `locally_minfty_le_real` -> `nbhs_minfty_le_real`
  + `lt_ereal_locally` -> `lt_ereal_nbhs`
  + `locally_pt_comp` -> `nbhs_pt_comp`
- in `derive.v`:
  + `derivable_locally` -> `derivable_nbhs`
  + `derivable_locallyP` -> `derivable_nbhsP`
  + `derivable_locallyx` -> `derivable_nbhsx`
  + `derivable_locallyxP` -> `derivable_nbhsxP`
- in `sequences.v`,
  + `cvg_comp_subn` -> `cvg_centern`,
  + `cvg_comp_addn` -> `cvg_shiftn`,
  + `telescoping` -> `telescope`
  + `sderiv1_series` -> `seriesSB`
  + `telescopingS0` -> `eq_sum_telescope`

### Removed

- in `topology.v`:
  + definitions `entourages`, `topologyOfBallMixin`, `ball_set`
  + lemmas `locally_E`, `entourages_filter`, `cvg_cauchy_ex`

## [0.3.1] - 2020-06-11

### Added

- in `boolp.v`, lemmas for classical reasoning `existsNP`, `existsPN`,
  `forallNP`, `forallPN`, `Nimply`, `orC`.
- in `classical_sets.v`, definitions for supremums: `ul`, `lb`,
  `supremum`
- in `ereal.v`:
  + technical lemmas `lee_ninfty_eq`, `lee_pinfty_eq`, `lte_subl_addr`, `eqe_oppLR`
  + lemmas about supremum: `ereal_supremums_neq0`
  + definitions:
    * `ereal_sup`, `ereal_inf`
  + lemmas about `ereal_sup`:
    * `ereal_sup_ub`, `ub_ereal_sup`, `ub_ereal_sup_adherent`
- in `normedtype.v`:
  + function `contract` (bijection from `{ereal R}` to `R`)
  + function `expand` (that cancels `contract`)
  + `ereal_pseudoMetricType R`

### Changed

- in `reals.v`, `pred` replaced by `set` from `classical_sets.v`
  + change propagated in many files

## [0.3.0] - 2020-05-26

This release is compatible with MathComp version 1.11+beta1.

The biggest change of this release is compatibility with MathComp
1.11+beta1.  The latter introduces in particular ordered types.
All norms and absolute values have been unified, both in their denotation `|_| and in their theory.

### Added

- `sequences.v`: Main theorems about sequences and series, and examples
  + Definitions:
    * `[sequence E]_n` is a special notation for `fun n => E`
    * `series u_` is the sequence of partial sums
    * `[normed S]` is the series of absolute values, if S is a series
    * `harmonic` is the name of a sequence,
       apply `series` to them to get the series.
  + Theorems:
    * lots of helper lemmas to prove convergence of sequences
    * convergence of harmonic sequence
    * convergence of a series implies convergence of a sequence
    * absolute convergence implies convergence of series
- in `ereal.v`: lemmas about extended reals' arithmetic
- in `normedtype.v`: Definitions and lemmas about generic domination,
  boundedness, and lipschitz
  + See header for the notations and their localization
  + Added a bunch of combinators to extract existential witnesses
  + Added `filter_forall` (commutation between a filter and finite forall)
- about extended reals:
  + equip extended reals with a structure of topological space
  + show that extended reals are hausdorff
- in `topology.v`, predicate `close`
- lemmas about bigmaxr and argmaxr
  + `\big[max/x]_P F = F [arg max_P F]`
  + similar lemma for `bigmin`
- lemmas for `within`
- add `setICl` (intersection of set with its complement)
- `prodnormedzmodule.v`
  + `ProdNormedZmodule` transfered from MathComp
  + `nonneg` type for non-negative numbers
- `bigmaxr`/`bigminr` library
- Lemmas `interiorI`, `setCU` (complement of union is intersection of complements),
  `setICl`, `nonsubset`, `setC0`, `setCK`, `setCT`, `preimage_setI/U`, lemmas about `image`

### Changed

- in `Rstruct.v`, `bigmaxr` is now defined using `bigop`
- `inE` now supports `in_setE` and `in_fsetE`
- fix the definition of `le_ereal`, `lt_ereal`
- various generalizations to better use the hierarchy of `ssrnum` (`numDomainType`,
  `numFieldType`, `realDomainType`, etc. when possible) in `topology.v`,
  `normedtype.v`, `derive.v`, etc.

### Renamed

- renaming `flim` to `cvg`
  + `cvg` corresponds to `_ --> _`
  + `lim` corresponds to `lim _`
  + `continuous`  corresponds to continuity
  + some suffixes `_opp`, `_add` ... renamed to `N`, `D`, ...
- big refactoring about naming conventions
  + complete the theory of `cvg_`, `is_cvg_` and `lim_` in normedtype.v
    with consistent naming schemes
  + fixed differential of `inv` which was defined on `1 / x` instead of `x^-1`
  + two versions of lemmas on inverse exist
    * one in realType (`Rinv_` lemmas), for which we have differential
    * a general one `numFieldType`  (`inv_` lemmas in normedtype.v, no differential so far, just continuity)
  + renamed `cvg_norm` to `cvg_dist` to reuse the name `cvg_norm` for
    convergence under the norm
- `Uniform` renamed to `PseudoMetric`
- rename `is_prop` to `is_subset1`

### Removed

- `sub_trans` (replaced by MathComp's `subrKA`)
- `derive.v` does not require `Reals` anymore
- `Rbar.v` is almost not used anymore

### Infrastructure

- NIX support
  + see `config.nix`, `default.nix`
  + for the CI also

### Misc
