# Changelog (unreleased)

## [Unreleased]

### Added
- in `topology.v`:
  + lemmas `continuous_subspaceT`, `subspaceT_continuous`
- in `constructive_ereal.v`
  + lemmas `fine_le`, `fine_lt`, `fine_abse`, `abse_fin_num`
- in `lebesgue_integral.v`
  + lemmas `integral_fune_lt_pinfty`, `integral_fune_fin_num`
- in `topology.v`
  + lemma `weak_subspace_open`
  + lemma `weak_ent_filter`, `weak_ent_refl`, `weak_ent_inv`, `weak_ent_split`,
      `weak_ent_nbhs`
  + definition `map_pair`, `weak_ent`, `weak_uniform_mixin`, `weak_uniformType`
  + lemma `sup_ent_filter`, `sup_ent_refl`, `sup_ent_inv`, `sup_ent_split`,
      `sup_ent_nbhs`
  + definition `sup_ent`, `sup_uniform_mixin`, `sup_uniformType`
  + definition `product_uniformType`
  + lemma `uniform_entourage`
  + definition `weak_ball`, `weak_pseudoMetricType`
  + lemma `weak_ballE`
  + lemma `finI_from_countable`
- in `cardinality.v`
  + lemmas `eq_card1`, `card_set1`, `card_eqSP`, `countable_n_subset`,
     `countable_finite_subset`, `eq_card_fset_subset`, `fset_subset_countable`
- in `classical_sets.v`
  + lemmas `IIDn`, `IISl`
- in `constructive_ereal.v`:
  + lemmas `gte_addl`, `gte_addr`
  + lemmas `gte_daddl`, `gte_daddr`
  + lemma `lte_spadder`, `lte_spaddre`
  + lemma `lte_spdadder`

### Changed
- in `topology.v`
  + definition `fct_restrictedUniformType` changed to use `weak_uniformType`
  + definition `family_cvg_topologicalType` changed to use `sup_uniformType`

- in `constructive_ereal.v`:
  + lemmas `lee_paddl`, `lte_paddl`, `lee_paddr`, `lte_paddr`,
    `lte_spaddr`, `lee_pdaddl`, `lte_pdaddl`, `lee_pdaddr`,
    `lte_pdaddr`, `lte_spdaddr` generalized to `realDomainType`
- in `constructive_ereal.v`:
  + generalize `lte_addl`, `lte_addr`, `gte_subl`, `gte_subr`,
    `lte_daddl`, `lte_daddr`, `gte_dsubl`, `gte_dsubr`

### Renamed

- in `topology.v`:
  + renamed `continuous_subspaceT` to `continuous_in_subspaceT`
- in `constructive_ereal.v`:
  + `lte_spdaddr` -> `lte_spdaddre`

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr`, renamed `lte_spaddre`

### Removed

### Infrastructure

### Misc
