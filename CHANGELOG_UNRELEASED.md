# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal_normedtype.v`:
  + lemma `ge0_cvgMly`

- new file `sub_pmf.v`:
  + definition `discrete_measurable_space`
  + mixin `isSubPmf`, factory `uniq_isSubPmf`, structure `SubPmf`,
    notation `R.-pmf T`
  + definition `sub_pmf`, lemma `sub_pmfP`
  + definition `measure_of_pmf`
  + definition `dinsupp`, abbreviation `dweight`
  + definitions `pmf_prob`, `pmf_cprob`, `pmf_expectation`,
    `pmf_cexpectation`, notations `\P_[mu] E`, `\P_[mu, A] E`,
    `\E_[mu] f`, `\E_[mu, A] f`
  + definition `pmf_esummable`
  + definitions `pmf_zero`, `pmf_restr`, `pmf_count`, `pmf_ret`,
    `pmf_uniform`, `pmf_flip`
  + definition `pmf_bind`, notation `\bind_(i <- d) E`,
    definitions `pmf_bindr`, `pmf_iter`
  + definition `pmf_lim`, notation `\lim_(n) E`
  + definition `pmf_margin`, abbreviations `pmf1`, `pmf2`,
    definition `pmf_swap`

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)

### Renamed

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

### Removed

### Infrastructure

### Misc
