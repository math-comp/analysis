# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal_normedtype.v`:
  + lemma `ge0_cvgMly`

- new file `uniform_metrizable.v`

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)

- from `pseudometric_structure.v` to `uniform_structure.v`:
  + definition `entourage_`

- from `separation_axioms.v` to `uniform_metrizable.v`:
  + module `countable_uniform`
  + notation `countable_uniform`
  + definition `sup_pseudometric`
  + module `gauge`
    * definition `gauge`
    * lemma `iter_split_ent`
    * lemma `gauge_ent`
    * lemma `gauge_filter`
    * lemma `gauge_refl`
    * lemma `gauge_inv`
    * lemma `gauge_split`
    * lemma `gauge_countable_uniformity`
    * definition `type`
  + lemma `uniform_pseudometric_sup`

- from `separation_axioms.v` to `topology_structure.v`:
  + definition `perfect_set`
  + lemmas `perfectP`, `perfectTP`, `perfectTP_ex`

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
