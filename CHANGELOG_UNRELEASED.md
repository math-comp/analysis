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

- in `exp.v`:
  + lemma `norm_expR`

- in `constructive_ereal.v`:
  + lemma `expe0`, `mule0n`, `muleS`

- in `exp.v`:
  + lemmas `expeR_eqy`
  + lemmas `lt0_powR1`, `powR_eq1`
  + definition `lne`
  + lemmas `le0_lneNy`, `lne_EFin`, `expeRK`, `lneK`, `lneK_eq`, `lne1`, `lneM`, 
    `lne_inj`, `lneV`, `lne_div`, `lte_lne`, `lee_lne`, `lneXn`, `le_lne1Dx`, 
    `lne_sublinear`, `lne_ge0`, `lne_lt0`, `lne_gt0`, `le1_lne_le0`

### Changed

### Renamed

- in `lebesgue_stieltjes_measure.v`:
  + `cumulativeNy0` -> `cumulativeNy`
  + `cumulativey1` -> `cumulativey`

- in `exp.v`:
  + `ltr_expeR` -> `lte_expeR`
  + `ler_expeR` -> `lee_expeR`

### Generalized

- in `functions.v`
  + lemma `fct_sumE` (from a pointwise equality to a functional one)

### Deprecated

### Removed

### Infrastructure

### Misc
