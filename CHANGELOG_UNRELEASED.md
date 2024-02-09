# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`
  + lemma `ln_lt0`

- in `lebesgue_integral.v`
  + lemma `ge0_integralZr`

### Changed
- moved from `topology.v` to `function_spaces.v`: `prod_topology`, 
    `product_topology_def`, `proj_continuous`, `dfwith_continuous`, 
    `proj_open`, `hausdorff_product`, `tychonoff`, `perfect_prod`, 
    `perfect_diagonal`, `zero_dimension_prod`, `totally_disconnected_prod`, 
    `separate_points_from_closed`, `weak_sep_cvg`, `weak_sep_nbhsE`, 
    `weak_sep_openE`, `join_product`, `join_product_continuous`, 
    `join_product_open`, `join_product_inj`, `join_product_weak`, `fct_ent`, 
    `fct_ent_filter`, `fct_ent_refl`, `fct_ent_inv`, `fct_ent_split`, 
    `cvg_fct_entourageP`, `fun_complete`, `fct_ball`, `fct_ball_center`, 
    `fct_ball_sym`, `fct_ball_triangle`, `fct_entourage`, `cvg_switch_1`, 
    `cvg_switch_2`, `cvg_switch`, `uniform_fun`, `uniform_nbhs`, 
    `uniform_entourage`, `restricted_cvgE`, `pointwise_cvgE`, 
    `uniform_fun_family`, `uniform_set1`, `uniform_subset_nbhs`, 
    `uniform_subset_cvg`, `pointwise_uniform_cvg`, `cvg_sigL`, `eq_in_close`, 
    `hausdorrf_close_eq_in`, `uniform_restrict_cvg`, `uniform_nbhsT`, 
    `cvg_uniformU`, `cvg_uniform_set0`, `fam_cvgP`, `family_cvg_subset`, 
    `family_cvg_finite_covers`, `fam_cvgE`, `fam_nbhs`, `fam_compact_nbhs`, 
    `compact_open`, `compact_openK`, `compact_openK_nbhs`, 
    `compact_open_of_nbhs`, `compact_open_def`, `compact_open_cvgP`, 
    `compact_open_open`, `compact_open_fam_compactP`, `compactly_in`, 
    `compact_cvg_within_compact`, `uniform_limit_continuous`, 
    `uniform_limit_continuous_subspace`, `singletons`, 
    `pointwise_cvg_family_singleton`, `pointwise_cvg_compact_family`, 
    `pointwise_cvgP`, `equicontinuous`, `equicontinuous_subset`, 
    `equicontinuous_subset_id`, `equicontinuous_continuous_for`, 
    `equicontinuous_continuous`, `pointwise_precompact`, 
    `pointwise_precompact_subset`, `pointwise_precompact_precompact`, 
    `uniform_pointwise_compact`, `precompact_pointwise_precompact`, 
    `pointwise_cvg_entourage`, `equicontinuous_closure`, `small_ent_sub`, 
    `pointwise_compact_cvg`, `pointwise_compact_closure`, 
    `pointwise_precompact_equicontinuous`, `compact_equicontinuous`, 
    `precompact_equicontinuous`, `Ascoli`, `continuous_curry`, 
    `continuous_uncurry_regular`, `continuous_uncurry`, `curry_continuous`, and 
    `uncurry_continuous`.

- move from `kernel.v` to `measure.v`
  + definition `mset`, `pset`, `pprobability`
  + lemmas `lt0_mset`, `gt1_mset`

- in `measure.v`:
  + lemma `sigma_finiteP` generalized to an equivalence and changed to use `[/\ ..., .. & ....]`

### Renamed

- in `constructive_ereal.v`:
  + `lee_addl` -> `leeDl`
  + `lee_addr` -> `leeDr`
  + `lee_add2l` -> `leeD2l`
  + `lee_add2r` -> `leeD2r`
  + `lee_add` -> `leeD`
  + `lee_sub` -> `leeB`
  + `lee_add2lE` -> `leeD2lE`
  + `lte_add2lE` -> `lteD2lE`
  + `lee_oppl` -> `leeNl`
  + `lee_oppr` -> `leeNr`
  + `lte_oppr` -> `lteNr`
  + `lte_oppl` -> `lteNl`
  + `lte_add` -> `lteD`
  + `lte_addl` -> `lteDl`
  + `lte_addr` -> `lteDr`

### Generalized

### Deprecated

### Removed

- in `topology.v`:
  + definition `pointwise_fun`
  + module `PtwsFun`

### Infrastructure

### Misc
