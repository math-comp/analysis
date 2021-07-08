# Changelog (unreleased)

## [Unreleased]

### Added

- in `boolp.v`:
  + lemmas `orA`, `andA`
- in `measure.v`:
  + definition `seqDU`
  + lemmas `trivIset_seqDU`, `bigsetU_seqDU`, `seqDU_bigcup_eq`, `seqDUE`

### Changed

- in `normedtype.v`:
  + remove useless parameter from lemma `near_infty_natSinv_lt`
- in `sequences.v`:
  + lemmas `seriesN`, `seriesD`, `seriesZ`, `is_cvg_seriesN`, `lim_seriesN`,
    `is_cvg_seriesZ`, `lim_seriesZ`, `is_cvg_seriesD`, `lim_seriesD`,
    `is_cvg_seriesB`, `lim_seriesB`, `lim_series_le`, `lim_series_norm`
- in `classical_sets.v`:
  + lemmas `bigcup_image`, `bigcup_of_set1`
- in `boolp.v`:
  + definitions `equality_mixin_of_Type`, `choice_of_Type`
- in `measure.v`:
  + HB.mixin `AlgebraOfSets_from_RingOfSets`
  + HB.structure `AlgebraOfSets` and notation `algebraOfSetsType`
  + HB.instance `T_isAlgebraOfSets` in HB.builders `isAlgebraOfSets`
  + lemma `bigcup_set_cond`
- in `classical_sets.v`:
  + lemmas `bigcupD1`, `bigcapD1`
- in `measure.v`:
  + definition `measurable_fun`
  + lemma `adde_undef_nneg_series`
  + lemma `adde_def_nneg_series`
- in `measure.v`:
  + lemmas `cvg_geometric_series_half`, `epsilon_trick`
  + definition `measurable_cover`
  + lemmas `cover_measurable`, `cover_subset`
  + definition `mu_ext`
  + lemmas `le_mu_ext`, `mu_ext_ge0`, `mu_ext0`, `measurable_uncurry`,
    `mu_ext_sigma_subadditive`
  + canonical `outer_measure_of_measure`
- in `ereal.v`:
  + lemmas `ge0_adde_def`, `onee_neq0`, `mule0`, `mul0e`
  + lemmas `mulrEDr`, `mulrEDl`, `ge0_muleDr`, `ge0_muleDl`
  + lemmas `sume_distrl`, `sume_distrr`
  + lemmas `mulEFin`, `mule_neq0`, `mule_ge0`, `muleA`
  + lemma `muleE`
  + lemmas `muleN`, `mulNe`, `muleNN`, `gee_pmull`, `lee_addgt0Pr`
  + lemmas `lte_pdivr_mull`, `lte_pdivl_mull`, `mule_continuous`

### Changed

- in `ereal.v`:
  + change defintion `mule` such that 0 x oo = 0

### Renamed

### Removed

- in `boolp.v`:
  + definition `PredType`
  + local notation `predOfType`

### Infrastructure

### Misc
