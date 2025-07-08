# Changelog (unreleased)

## [Unreleased]

### Added

- in `unstable.v`:
  + lemma `sqrK`

- in `realfun.v`:
  + instance `is_derive1_sqrt`
- in `mathcomp_extra.v`:
  + lemmas `subrKC`, `sumr_le0`, `card_fset_sum1`

- in `functions.v`:
  + lemmas `fct_prodE`, `prodrfctE`

- in `exp.v:
  + lemma `norm_expR`

- in new file `gauss_integral_unbounded`
  + add lemmas `integral0y_gauss_fin_num`,
               `integral0y_u0`,
	       `integrable0y_u`,
	       `max_y_ge0`,
	       `u_dominates`,
	       `int0yu_fin_num`,
	       `cvgy_int0yu0`,
	       `derive1_int0yuE`,
	       `derivable_int0yu`,
	       `rcvg0_int0yu`,
	       `gauss_integration`

### Changed

### Renamed

- in `lebesgue_stieltjes_measure.v`:
  + `cumulativeNy0` -> `cumulativeNy`
  + `cumulativey1` -> `cumulativey`

### Generalized

- in `functions.v`
  + lemma `fct_sumE` (from a pointwise equality to a functional one)

### Deprecated

### Removed

- file `forms.v` (superseded by MathComp's `sesquilinear.v`)

### Infrastructure

### Misc
