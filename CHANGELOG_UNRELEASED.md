# Changelog (unreleased)

## [Unreleased]

### Added

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

- in `mathcomp_extra.v`:
  + lemma `bij_forall`

- in `normedtype.v`:
  + lemma `cvgyNP`

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

- in `filter.v` (new file):
  + lemma `in_nearW`

- in `topology.v`:
  + lemma `open_in_nearW`

- in `classical_sets.v`:
  + lemma `not_setD1`

- in `measure.v`:
  + lemma `measurable_fun_set1`
- in file `classical_orders.v`,
  + new definitions `big_lexi_order`, `same_prefix`, `first_diff`,
    `big_lexi_le`, and `start_with`.
  + new lemmas `same_prefix0`, `same_prefix_sym`, `same_prefix_leq`,
    `same_prefix_refl`, `same_prefix_trans`, `first_diff_sym`,
    `first_diff_unique`, `first_diff_SomeP`, `first_diff_NoneP`,
    `first_diff_lt`, `first_diff_eq`, `first_diff_dfwith`,
    `big_lexi_le_reflexive`, `big_lexi_le_anti`, `big_lexi_le_trans`,
    `big_lexi_le_total`, `start_with_prefix`, `leEbig_lexi_order`,
    `big_lexi_order_prefix_lt`, `big_lexi_order_prefix_gt`,
    `big_lexi_order_between`, and `big_lexi_order_interval_prefix`.

- in `exp.v`:
  + lemma `expR_gt1Dx`

- in `derive.v`:
  + lemma `exprn_derivable`
- in `sequences.v`:
  + lemma `nneseries_split_cond`
  + lemma `subset_lee_nneseries`

- in `lebesgue_measure.v`:
  + lemma `vitali_coverS`
  + lemma `vitali_theorem_corollary`

- in `normedtype.v`:
  + lemma `limf_esup_ge0`
- in `normedtype.v`:
  + lemma `nbhs_left_ltBl`
  + lemma `within_continuous_continuous`

- in `measure.v`:
  + lemma `measurable_fun_set0`

- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_itv_co`, `measurable_fun_itv_oc`, `measurable_fun_itv_cc`

- in `lebesgue_integral.v`:
  + lemma `integral_itv_bndoo`

- in `ftc.v`:
  + lemmas `increasing_image_oo`, `decreasing_image_oo`,
    `increasing_cvg_at_right_comp`, `increasing_cvg_at_left_comp`,
    `decreasing_cvg_at_right_comp`, `decreasing_cvg_at_left_comp`,
  + lemma `eq_integral_itv_bounded`.
  + lemmas `integration_by_substitution_decreasing`,
    `integration_by_substitution_oppr`,
    `integration_by_substitution_increasing`

### Changed

- in `numfun.v`:
  + lemma `gt0_funeposM` renamed to `ge0_funeposM`
    and hypothesis weakened from strict to large inequality
  + lemma `gt0_funenegM` renamed to `ge0_funenegM`
    and hypothesis weakened from strict to large inequality
  + lemma `lt0_funeposM` renamed to `le0_funeposM`
    and hypothesis weakened from strict to large inequality
  + lemma `lt0_funenegM` renamed to `le0_funenegM`
    and hypothesis weakened from strict to large inequality

- `theories/topology.v` split into `classical/filter.v` and `theories/topology.v`

- moved from `topology.v` to `filter.v`
  + definition `set_system`, coercion `set_system_to_set`
  + mixin `isFiltered`, structures `Filtered`, `PointedFiltered`
    (with resp. types `filteredType` and `pfilteredType`)
  + mixin `selfFiltered`
  + factory `hasNbhs`
  + structures `Nbhs`, `PointedNbhs`
    (with resp. types `nbhsType`, `pnbhsType`)
  + definitions `filter_from`, `filter_prod`
  + definitions `prop_near1`, `prop_near2`
  + notations `{near _, _}`, `\forall _ \near _, _`, `near _, _`,
    `{near _ & _, _}`, `\forall _ \near _ & _, _`, `\forall _ & _ \near _, _`,
    `\near _ & _, _`
  + lemmas `nearE`, `eq_near`, `nbhs_filterE`
  + module `NbhsFilter` (with definition `nbhs_simpl`)
  + definition `cvg_to`, notation ```_ `=>` _```
  + lemmas `cvg_refl`, `cvg_trans`, notation `_ --> _`
  + definitions `type_of_filter`, `lim_in`, `lim`
  + notations `[lim _ in _]`, `[cvg _ in _]`, `cvg`
  + definition `eventually`, notation `\oo`
  + lemmas `cvg_prod`, `cvg_in_ex`, `cvg_ex`, `cvg_inP`, `cvgP`, `cvg_in_toP`,
    `cvg_toP`, `dvg_inP`, `dvgP`, `cvg_inNpoint`, `cvgNpoint`
  + lemmas `nbhs_nearE`, `near_nbhs`, `near2_curry`, `near2_pair`, `filter_of_nearI`
  + definition `near2E`
  + module `NearNbhs` (with (re)definition `near_simpl` and ltac `near_simpl`)
  + lemma `near_swap`
  + classes `Filter`
  + lemmas `filter_setT`, `filterP_strong`
  + structure `filter_on`
  + definition `filter_class`
  + coercion `filter_filter'`
  + structure `pfilter_on`
  + definition `pfilter_class`
  + canonical `pfilter_filter_on`
  + coercion `pfilter_filter_on`
  + definiton `PFilterType`
  + instances `filter_on_Filter`, `pfilter_on_ProperFilter`
  + lemma `nbhs_filter_onE`, `near_filter_onE`
  + definition and canonical `trivial_filter_on`
  + lemmas `filter_nbhsT`, `nearT`, `filter_not_empty_ex`
  + lemma `filter_ex_subproof`, definition `filter_ex`
  + lemma `filter_getP`
  + record `in_filter`
  + module type `in_filter`, module `PropInFilter`, notation `prop_of`, definition `prop_ofE`,
    notation `_ \is_near _`, definition `is_nearE`
  + lemma `prop_ofP`
  + definition `in_filterT`
  + canonical `in_filterI`
  + lemma `filter_near_of`
  + fact `near_key`
  + lemmas `mark_near`, `near_acc`, `near_skip_subproof`
  + tactic notations `near=>`, `near:`, `near do _`
  + ltacs `just_discharge_near`, `near_skip`, `under_near`, `end_near`, `done`
  + lemmas `have_near`, `near`, `nearW`, `filterE`, `filter_app`, `filter_app2`,
    `filter_app3`, `filterS2`, `filterS3`, `filter_const`, `in_filter_from`,
    `near_andP`, `nearP_dep`, `filter2P`, `filter_ex2`, `filter_fromP`, `filter_fromTP`,
    `filter_from_filter`, `filter_fromT_filter`, `filter_from_proper`, `filter_bigI`,
    `filter_forall`, `filter_imply`
  + definition `fmap`
  + lemma `fmapE`
  + notations `_ @[_ --> _]`, `_ @[_ \oo]`, `_ @ _`, `limn`, `cvgn`
  + instances `fmap_filter`, `fmap_proper_filter`
  + definition `fmapi`, notations `_ `@[_ --> _]`, `_ `@ _`
  + lemma `fmapiE`
  + instances `fmapi_filter`. `fmapi_proper_filter`
  + lemmas `cvg_id`, `fmap_comp`, `appfilter`, `cvg_app`, `cvgi_app`, `cvg_comp`,
    `cvgi_comp`, `near_eq_cvg`, `eq_cvg`, `eq_is_cvg_in`, `eq_is_cvg`, `neari_eq_loc`,
    `cvg_near_const`
  + definition `continuous_at`, notation `continuous`
  + lemma `near_fun`
  + definition `globally`, lemma `globally0`, instances `globally_filter`, `globally_properfilter`
  + definition `frechet_filter`, instances `frechet_properfilter`, `frechet_properfilter_nat`
  + definition `at_point`, instance `at_point_filter`
  + instances `filter_prod_filter`, `filter_prod_proper`, canonical `prod_filter_on`
  + lemmas `filter_prod1`, `filter_prod2`
  + definition `in_filter_prod`
  + lemmas `near_pair`, `cvg_cst`, `cvg_snd`, `near_map`, `near_map2`, `near_mapi`,
    `filter_pair_set`, `filter_pair_near_of`
  + module export `NearMap`
  + lemmas `filterN`, `cvg_pair`, `cvg_comp2`
  + definition `cvg_to_comp_2`
  + definition `within`, lemmas `near_withinE`, `withinT`, `near_withinT`, `cvg_within`,
    `withinET`, instance `within_filter`, canonical `within_filter_on`,
    lemma `filter_bigI_within`
  + definition `subset_filter`, instance `subset_filter_filter`, lemma `subset_filter_proper`
  + definition `powerset_filter_from`, instance `powerset_filter_from_filter`
  + lemmas `near_small_set`, `small_set_sub`, `near_powerset_filter_fromP`,
    `powerset_filter_fromP`, `near_powerset_map`, `near_powerset_map_monoE`
  + definitions `principal_filter`, `principal_filter_type`
  + lemmas `principal_filterP`, `principal_filter_proper`
  + class `UltraFilter`, lemma `ultraFilterLemma`
  + lemmas `filter_image`, `proper_image`, `principal_filter_ultra`, `in_ultra_setVsetC`,
    `ultra_image`
  + instance `smallest_filter_filter`
  + fixpoint `filterI_iter`
  + lemmas `filterI_iter_sub`, `filterI_iterE`
  + definition `finI_from`
  + lemmas `finI_from_cover`, `finI_from1`, `finI_from_countable`, `finI_fromI`,
    `filterI_iter_finI`, `filterI_iter_finI`
  + definition `finI`
  + lemmas `finI_filter`, `filter_finI`, `meets_globallyl`, `meets_globallyr`,
    `meetsxx`, `proper_meetsxx`

- changed when moved from `topology.v` to `filter.v`
  + `Build_ProperFilter` -> `Build_ProperFilter_ex`
  + `ProperFilter'` -> `ProperFilter`
  + remove notation `ProperFilter`

- moved from `topology.v` to `mathcomp_extra.v`:
  + lemma `and_prop_in`
  + lemmas `mem_inc_segment`, `mem_inc_segment`

- moved from `topology.v` to `boolp.v`:
  + lemmas `bigmax_geP`, `bigmax_gtP`, `bigmin_leP`, `bigmin_ltP`

- moved from `topology.v` to `separation_axioms.v`: `set_nbhs`, `set_nbhsP`,
    `accessible_space`, `kolmogorov_space`, `hausdorff_space`,
    `compact_closed`, `discrete_hausdorff`, `compact_cluster_set1`,
    `compact_precompact`, `open_hausdorff`, `hausdorff_accessible`,
    `accessible_closed_set1`, `accessible_kolmogorov`,
    `accessible_finite_set_closed`, `subspace_hausdorff`, `order_hausdorff`,
    `ball_hausdorff`, `Rhausdorff`, `close`, `closeEnbhs`, `closeEonbhs`,
    `close_sym`, `cvg_close`, `close_refl`, `cvgx_close`, `cvgi_close`,
    `cvg_toi_locally_close`, `closeE`, `close_eq`, `cvg_unique`, `cvg_eq`,
    `cvgi_unique`, `close_cvg`, `lim_id`, `lim_near_cst`, `lim_cst`,
    `entourage_close`, `close_trans`, `close_cvgxx`, `cvg_closeP`,
    `ball_close`, `normal_space`, `regular_space`, `compact_regular`,
    `uniform_regular`, `totally_disconnected`, `zero_dimensional`,
    `discrete_zero_dimension`, `zero_dimension_totally_disconnected`,
    `zero_dimensional_ray`, `type`, `countable_uniform_bounded`,
    `countable_uniform`, `sup_pseudometric`, `countable_uniformityT`, `gauge`,
    `iter_split_ent`, `gauge_ent`, `gauge_filter`, `gauge_refl`, `gauge_inv`,
    `gauge_split`, `gauge_countable_uniformity`, `uniform_pseudometric_sup`,
    `perfect_set`, `perfectTP`, and `perfectTP_ex`.
### Renamed
- in file `topology.v` -> `separation_axioms.v`
  + `totally_disconnected_cvg` -> `zero_dimensional_cvg`.
  + `perfect_set2` -> `perfectTP_ex`


### Generalized

- in `constructive_ereal.v`:
  + lemmas `maxeMr`, `maxeMl`, `mineMr`, `mineMr`:
    hypothesis weakened from strict inequality to large inequality
- in `lebesgue_integral.v`:
  + lemma `integral_setD1_EFin`
  + lemmas `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`
  + lemmas `Rintegral_itv_bndo_bndc`, `Rintegral_itv_obnd_cbnd`

- in `exp.v`:
  + lemmas `expR_ge1Dx` and `expeR_ge1Dx` (remove hypothesis)
  + lemma `le_ln1Dx` (weaken hypothesis)

- in `sequences.v`:
  + lemma `eseries_mkcond`
  + lemma `nneseries_tail_cvg`

- in `derive.v`:
  + lemma `derivableX`

### Deprecated

- in `separation_axioms.v`:
  + definition `cvg_toi_locally_close`
- in `realfun.v`:
  + lemma `lime_sup_ge0`

### Removed

- in `topology.v`:
  + notation `[filteredType _ of _]`
  + definition `fmap_proper_filter'`
  + definition `filter_map_proper_filter'`
  + definition `filter_prod_proper'`
- in `sequences.v`:
  + notation `nneseries_mkcond` (was deprecated since 0.6.0)

- in `constructive_ereal.v`:
  + notation `lte_spaddr` (deprecated since 0.6)

- in `normedtype.v`:
  + notation `normmZ` (deprecated since 0.6.0)
  + notation `nbhs_image_ERFin` (deprecated since 0.6.0)
  + notations `ereal_limrM`, `ereal_limMr`, `ereal_limN` (deprecated since 0.6.0)
  + notation `norm_cvgi_map_lim` (deprecated since 0.6.0)
  + notations `ereal_cvgN`, `ereal_is_cvgN`, `ereal_cvgrM`, `ereal_is_cvgrM`,
    `ereal_cvgMr`, `ereal_is_cvgMr`, `ereal_cvgM` (deprecated since 0.6.0)
  + notation `cvg_dist`, lemma `__deprecated__cvg_dist` (deprecated since 0.6.0)
  + notation `cvg_dist2`, lemma `__deprecated__cvg_dist2` (deprecated since 0.6.0)
  + notation `cvg_dist0`, lemma `__deprecated__cvg_dist0` (deprecated since 0.6.0)
  + notation `ler0_addgt0P`, lemma `__deprecated__ler0_addgt0P` (deprecated since 0.6.0)
  + notation `cvg_bounded_real`, lemma `__deprecated__cvg_bounded_real` (deprecated since 0.6.0)
  + notation `linear_continuous0`, lemma `__deprecated__linear_continuous0` (deprecated since 0.6.0)

- in `constructive_ereal.v`:
  + notation `gte_opp` (deprecated since 0.6.0)
  + lemmas `daddooe`, `daddeoo`
  + notations `desum_ninftyP`, `desum_ninfty`, `desum_pinftyP`, `desum_pinfty` (deprecated since 0.6.0)
  + notation `eq_pinftyP` (deprecated since 0.6.0)

- in `sequences.v`:
  + notation `squeeze`, lemma `__deprecated__squeeze` (deprecated since 0.6.0)
  + notation `cvgPpinfty`, lemma `__deprecated__cvgPpinfty` (deprecated since 0.6.0)
  + notation `cvgNpinfty`, lemma `__deprecated__cvgNpinfty` (deprecated since 0.6.0)
  + notation `cvgNninfty`, lemma `__deprecated__cvgNninfty` (deprecated since 0.6.0)
  + notation `cvgPninfty`, lemma `__deprecated__cvgPninfty` (deprecated since 0.6.0)
  + notation `ger_cvg_pinfty`, lemma `__deprecated__ger_cvg_pinfty` (deprecated since 0.6.0)
  + notation `ler_cvg_ninfty`, lemma `__deprecated__ler_cvg_ninfty` (deprecated since 0.6.0)
  + notation `lim_ge`, lemma `__deprecated__lim_ge` (deprecated since 0.6.0)
  + notation `lim_le`, lemma `__deprecated__lim_le` (deprecated since 0.6.0)

### Infrastructure

### Misc
