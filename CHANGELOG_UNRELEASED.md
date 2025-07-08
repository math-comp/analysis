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

- in `reals.v`:
  + definition `irrational`
  + lemmas `irrationalE`, `rationalP` 

- in `topology_structure.v`:
  + lemmas `denseI`, `dense0`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `dense_set1C`

- new file `borel_hierarchy.v`:
  + definitions `Gdelta`, `Fsigma`
  + lemmas `closed_Fsigma`, `Gdelta_measurable`, `Gdelta_subspace_open`,
    `irrational_Gdelta`, `not_rational_Gdelta`

### Changed

- moved from `pi_irrational.v` to `reals.v` and changed
  + definition `rational`

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
