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

### Changed

- in `topology.v`:
  + generalize `cluster_cvgE`, `fam_cvgE`, `ptws_cvg_compact_family`
  + rewrite `equicontinuous` and `pointwise_precompact` to use index 

### Renamed

### Removed

### Infrastructure

### Misc