# Changelog (unreleased)

## [Unreleased]

### Added

- in `topology.v`:
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

### Changed

- in `topology.v`:
  + generalize `cluster_cvgE`, `fam_cvgE`, `ptws_cvg_compact_family`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index 
- in `Rstruct.v`:
  + statement of lemma `completeness'`, renamed to `Rcondcomplete`
  + statement of lemma `real_sup_adherent`
- in `ereal.v`:
  + statements of lemmas `ub_ereal_sup_adherent`, `lb_ereal_inf_adherent`
- in `reals.v`:
  + definition `sup`
  + statements of lemmas `sup_adherent`, `inf_adherent`

### Renamed

### Removed

- `has_sup1`, `has_inf1` moved from `reals.v` to `classical_sets.v`
- in `reals.v`:
  + type generalization of `has_supPn`
- in `classical_sets.v`:
  + `supremums_set1` -> `supremums1`
  + `infimums_set1` -> `infimums1`
- in `Rstruct.v`:
  + definition `real_sup`
  + lemma `real_sup_is_lub`, `real_sup_ub`, `real_sup_out`
- in `reals.v`:
  + field `sup` from `mixin_of` in module `Real`

### Infrastructure

### Misc