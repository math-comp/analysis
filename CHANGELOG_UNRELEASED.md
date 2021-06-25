# Changelog (unreleased)

## [Unreleased]

### Added

- in `sequences.v`:
  + lemmas `seriesN`, `seriesD`, `seriesZ`, `is_cvg_seriesN`, `lim_seriesN`,
    `is_cvg_seriesZ`, `lim_seriesZ`, `is_cvg_seriesD`, `lim_seriesD`,
    `is_cvg_seriesB`, `lim_seriesB`, `lim_series_le`, `lim_series_norm`
  + lemma `adde_def_nneg_series`
- in `measure.v`:
  + lemmas `epsilon_trick`, 
  + definition `measurable_cover`
  + lemmas `cover_measurable`, `cover_subset`
  + definition `mu_ext`
  + lemmas `le_mu_ext`, `mu_ext_ge0`, `mu_ext0`, `measurable_uncurry`,
    `mu_ext_sigma_subadditive`
  + canonical `outer_measure_of_measure`

### Changed

- in `measure.v`:
  + generalize lemma `eq_bigcupB_of`
- in `ereal.v`, definition `adde_undef` changed to `adde_def`
  + consequently, the following lemmas changed:
    * in `ereal.v`, `adde_undefC` renamed to `adde_defC`,
      `fin_num_adde_undef` renamed to `fin_num_adde_def`
    * in `sequences.v`, `ereal_cvgD` and `ereal_limD` now use hypotheses with `adde_def`
- in `sequences.v`:
  + generalize `{in,de}creasing_seqP`, `non{in,de}creasing_seqP` from `numDomainType`
    to `porderType`

### Renamed

### Removed

### Infrastructure

### Misc
