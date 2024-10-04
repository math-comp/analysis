# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

- The file `topology.v` has been split into several files in the directory 
  `topology_theory`. Unless stated otherwise, definitions, lemmas, etc. 
  have been moved without changes. The same import will work as before, 
  `Require Import topology.v`.

- in `matrix_topology.v` (new file):
  + lemmas `mx_ball_center`, `mx_ball_sym`, `mx_ball_triangle`, `mx_entourage`
    are now `Local`

- in `weak_topology.v` (new file):
  + lemmas `wopT`, `wopI`, `wop_bigU` are now `Local`

- in `supremum_topology.v` (new file):
  + lemmas `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
    `sup_ent_nbhs` are now `Local`

- The function `map_pair` was moved from `topology.v` to `mathcomp_extra.v`.

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
- in file `normedtype.v`,
  + new definition `type`.
  + new lemmas `normal_completely_regular`, `completely_reg_opc`,
    `nbhs_opc_weakE`, `locally_compact_completely_regular`, and
    `completely_regular_regular`.
- in file `topology.v`,
  + new definitions `one_point_compactification`, and `one_point_nbhs`.
  + new lemmas `compact_normal_local`, `compact_normal`, `opc_compact`,
    `opc_some_nbhs`, `opc_some_continuous`, `opc_open_some`,
    `opc_weak_topology`, and `opc_hausdorff`.

### Changed

- in file `normedtype.v`, 
     changed `completely_regular_space` to depend on uniform separators
     which removes the dependency on R.  The old formulation can be 
     recovered easily with uniform_separatorP.
- in file `filter.v` generalized `smallest_filter_finI`.

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

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
