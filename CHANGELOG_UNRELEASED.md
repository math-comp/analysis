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
- in `hoelder.v`
  + lemma `hoelder_conj_ge1`

- in `realfun.v`:
  + lemmas `derivable_oy_continuous_within_itvcy`,
           `derivable_oy_continuous_within_itvNyc`,
  + lemmas `derivable_oo_continuous_bndW`,
           `derivable_oy_continuous_bndW_oo`,
           `derivable_oy_continuous_bndW`,
           `derivable_Nyo_continuous_bndW_oo`,
           `derivable_Nyo_continuous_bndW`

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
