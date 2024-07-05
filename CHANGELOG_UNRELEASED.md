# Changelog (unreleased)

## [Unreleased]

### Added

### Changed

- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in `lebesgue_integral.v`:
  + lemma `cst_mfun_subproof` now a `Let`

### Renamed

### Generalized

- in `lebesgue_integral.v`:
  + generalized from `sigmaRingType`/`realType` to `sigmaRingType`
    * mixin `isMeasurableFun`
    * structure `MeasurableFun`
	* definition `mfun`
    * lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`
  + generalized from `measurableType`/`realType` to `sigmaRingType`/`realType`
    * lemmas `cst_mfun_subproof`, `mfun_cst`
    * definition `cst_mfun`

### Deprecated

### Removed

- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`

### Infrastructure

### Misc
