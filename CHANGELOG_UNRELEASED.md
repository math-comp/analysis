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
- in `topology.v`:
  + lemmas `continuous_subspace0`, `continuous_subspace1`

- in `realfun.v`:
  + Instance for `GRing.opp` over real intervals

### Changed
- in `realfun.v`
  + lemmas `itv_continuous_inj_le`, `itv_continuous_inj_ge`,
     `itv_continuous_inj_mono`, `segment_continuous_inj_le`,
     `segment_continuous_inj_ge`, `segment_can_le` ,
     `segment_can_ge`, `segment_can_mono`,
     `segment_continuous_surjective`, `segment_continuous_le_surjective`,
     `segment_continuous_ge_surjective`, `continuous_inj_image_segment`,
     `continuous_inj_image_segmentP`, `segment_continuous_can_sym`,
     `segment_continuous_le_can_sym`, `segment_continuous_ge_can_sym`,
     `segment_inc_surj_continuous`, `segment_dec_surj_continuous`,
     `segment_mono_surj_continuous`, `segment_can_le_continuous`,
     `segment_can_ge_continuous`, `segment_can_continuous`
     all have "{in I, continuous f}" replaced by "{within I, continuous f}"


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
