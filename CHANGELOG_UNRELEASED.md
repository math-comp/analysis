# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

- Requires:
  + MathComp >= 1.12
- in `boolp.v`:
  + lemmas `contra_not`, `contra_notT`, `contra_notN`, `contra_not_neq`, `contraPnot`
    are now provided by MathComp 1.12
- in `normedtype.v`:
  + lemmas `ltr_distW`, `ler_distW` are now provided by MathComp 1.12 as lemmas
    `ltr_distlC_subl` and `ler_distl_subl`
  + lemmas `maxr_real` and `bigmaxr_real` are now provided by MathComp 1.12 as
    lemmas `max_real` and `bigmax_real`
  + definitions `isBOpen` and `isBClosed` are replaced by the definition `bound_side`
  + definition `Rhull` now uses `BSide` instead of `BOpen_if`

### Renamed

### Removed

- Drop support for MathComp 1.11

### Infrastructure

### Misc
