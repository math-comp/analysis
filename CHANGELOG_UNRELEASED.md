# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemma `ltgte_fin_num`

- in `num_normedtype.v`:
  + lemma `nbhs_infty_gtr`

### Changed

- in `lebesgue_stieltjes_measure.v` specialized from `numFieldType` to `realFieldType`:
  + lemma `nondecreasing_right_continuousP` 
  + definition `CumulativeBounded`

- in `lebesgue_stieltjes_measure.v`, according to generalization of `Cumulative`, modified:
  + lemmas `wlength_ge0`, `cumulative_content_sub_fsum`, `wlength_sigma_subadditive`, `lebesgue_stieltjes_measure_unique`
  + definitions `lebesgue_stieltjes_measure`, `completed_lebesgue_stieltjes_measure`

### Renamed

- in `lebesgue_stieltjes_measure.v`:
  + `cumulativeNy0` -> `cumulativeNy`
  + `cumulativey1` -> `cumulativey`
	+ `cumulativey1` -> `cumulativey`

### Generalized

- in `lebesgue_stieltjes_measure.v` generalized (codomain is now an `orderNbhsType`):
  + lemma `right_continuousW`
  + record `isCumulative`
  + definition `Cumulative`

### Deprecated

### Removed

### Infrastructure

### Misc
