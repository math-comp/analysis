# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

- in `lebesgue_integral.v`:
  + structure `SimpleFun` now inside a module `HBSimple`
  + structure `NonNegSimpleFun` now inside a module `HBNNSimple`
  + lemma `cst_nnfun_subproof` has now a different statement
  + lemma `indic_nnfun_subproof` has now a different statement


### Renamed

### Generalized

- in `lebesgue_integral.v`:
  + generalized from `sigmaRingType`/`realType` to `sigmaRingType`/`sigmaRingType`
    * mixin `isMeasurableFun`
    * structure `MeasurableFun`
	* definition `mfun`
    * lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`

### Deprecated

### Removed

- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`

- in `cardinality.v`:
  + lemma `cst_fimfun_subproof`

- in `lebesgue_integral.v`:
  + lemma `cst_mfun_subproof` (use lemma `measurable_cst` instead)
  + lemma `cst_nnfun_subproof` (turned into a `Let`)
  + lemma `indic_mfun_subproof` (use lemma `measurable_fun_indic` instead)

### Infrastructure

### Misc
