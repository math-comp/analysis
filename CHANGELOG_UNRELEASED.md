# Changelog (unreleased)

## [Unreleased]

### Added
- in `topology.v`:
  + lemmas `continuous_subspaceT`, `subspaceT_continuous`
- in `constructive_ereal.v`
  + lemmas `fine_le`, `fine_lt`, `fine_abse`, `abse_fin_num`
- in `lebesgue_integral.v`
  + lemmas `integral_fune_lt_pinfty`, `integral_fune_fin_num`
  + lemma `weak_subspace_open`
  + definition `powerset_filter_from`
  + globals `powerset_filter_from_filter`, 
  + lemmas `near_small_set`, `small_set_sub`, `near_powerset_filter_fromP`
  + lemmas `withinET`, `closureEcvg`, `entourage_sym`, `fam_nbhs`
  + definition `near_covering`
  + lemma `compact_near_coveringP`
  + lemma `continuous_localP`, `equicontinuous_subset_id`
  + lemmas `ptws_cvg_entourage`, `equicontinuous_closure`, `ptws_compact_cvg`
    `ptws_compact_closed`, `ascoli_forward`
  + lemmas `precompact_pointwise_precompact`, `precompact_equicontinuous`,
    `ascoli_theorem`
- in file `classical_sets.v`
  + lemma `set_bool`
- in file `topology.v`:
  + definition `principal_filter` `discrete_space`
  + lemma `principal_filterP`, `principal_filter_proper`, 
      `principa;_filter_ultra`
  + canonical `bool_discrete_filter`
  + lemma `compactU`
  + lemma `discrete_sing`, `discrete_nbhs`, `discrete_open`, `discrete_set1`,
      `discrete_closed`, `discrete_cvg`, `discrete_hausdorff`
  + canonical `bool_discrete_topology`
  + definition `discrete_topological_mixin`
  + lemma `discrete_bool`, `bool_compact`
- in `reals.v`:
  + lemma `floor_natz`
- in file `topology.v`:
  + definition `frechet_filter`, instances `frechet_properfilter`, and `frechet_properfilter_nat`
- in `Rstruct.v`:
  + lemmas `Rsupremums_neq0`, `Rsup_isLub`, `Rsup_ub`
- in `classical_sets.v`:
  + lemma `supremum_out`
  + definition `isLub`
  + lemma `supremum1`
- in `reals.v`:
  + lemma `opp_set_eq0`, `ubound0`, `lboundT`
- in `topology.v`
  + lemma `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`, `weak_ent_split`,
      `weak_ent_nbhs`
  + definition `map_pair`, `weak_ent`, `weak_uniform_mixin`, `weak_uniformType`
  + lemma `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
      `sup_ent_nbhs`
  + definition `sup_ent`, `sup_uniform_mixin`, `sup_uniformType`
  + definition `product_uniformType`
  + lemma `uniform_entourage`

### Changed
- in `topology.v`
  + definition `fct_restrictedUniformType` changed to use `weak_uniformType`
  + definition `family_cvg_topologicalType` changed to use `sup_uniformType`

### Renamed

- in `topology.v`:
  + renamed `continuous_subspaceT` to `continuous_in_subspaceT`

### Removed

### Infrastructure

### Misc
