# Changelog (unreleased)

## [Unreleased]

### Added

- in `tvs.v`:
  + HB.structure `Tvs`
  + HB.factory `TopologicalLmod_isTvs`
  + lemma `nbhs0N`
  + lemma `nbhsN`
  + lemma `nbhsT`
  + lemma `nbhsB`
  + lemma `nbhs0Z`
  + lemma `nbhZ`
  + HB.Instance of a Tvs od R^o
  + HB.Instance of a Tvs on a product of Tvs
  
### Changed

- in normedtype.v
  + HB structure `normedModule` now depends on a Tvs
    instead of a Lmodule
  + Factory `PseudoMetricNormedZmod_Lmodule_isNormedModule` becomes
    `PseudoMetricNormedZmod_Tvs_isNormedModule`
  + Section `prod_NormedModule` now depends on a `numFieldType`
  
### Renamed
- in normedtype.v
  + Section `regular_topology` to `standard_topology`
  
### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
