# Changelog (unreleased)

## [Unreleased]

### Added

- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`

- in `lebesgue_measure.v`:
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`

### Changed

- `mnormalize` moved from `kernel.v` to `measure.v` and generalized
- in `constructive_ereal.v`:
  + `lee_adde` renamed to `lee_addgt0Pr` and turned into a reflect
  + `lee_dadde` renamed to `lee_daddgt0Pr` and turned into a reflect

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
