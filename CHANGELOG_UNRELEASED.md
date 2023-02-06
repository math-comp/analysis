# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + canonical `unit_pointedType`
- in `measure.v`:
  + definition `finite_measure`
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`
- in file `classical_sets.v`,
  + new lemma `preimage_range`.
- in file `topology.v`,
  + new definitions `hausdorff_accessible`, `separates_points_from_closed`, and 
    `join_product`.
  + new lemmas `weak_sep_cvg`, `weak_sep_nbhsE`, `weak_sep_openE`, 
    `join_product_continuous`, `join_product_open`, `join_product_inj`, and 
    `join_product_weak`.
- in `boolp.v`:
  + lemma `forallp_asboolPn2`

### Changed

- in `fsbigop.v`:
  + implicits of `eq_fsbigr`
- in `topology.v`:
  + `Topological.ax2`

### Renamed

### Generalized

- in `esum.v`:
  + lemma `esum_esum`

### Deprecated

### Removed

- in `esum.v`:
  + lemma `fsbig_esum`

### Infrastructure

### Misc
