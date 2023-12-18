# Changelog (unreleased)

## [Unreleased]

### Added

- in `lebesgue_stieltjes_measure.v`:
  + `sigma_finite_measure` HB instance on `lebesgue_stieltjes_measure`

- in `lebesgue_measure.v`:
  + `sigma_finite_measure` HB instance on `lebesgue_measure`

- in `lebesgue_integral.v`:
  + `sigma_finite_measure` instance on product measure `\x`

- file `contra.v`
- in `contra.v`
  + lemma `assume_not`
  + tactic `assume_not`
  + lemma `absurd_not`
  + tactics `absurd_not`, `contrapose`
  + tactic notations `contra`, `contra : constr(H)`, `contra : ident(H)`,
    `contra : { hyp_list(Hs) } constr(H)`, `contra : { hyp_list(Hs) } ident(H)`,
	 `contra : { - } constr(H)`
  + lemma `absurd`
  + tactic notations `absurd`, `absurd constr(P)`, `absurd : constr(H)`,
    `absurd : ident(H)`, `absurd : { hyp_list(Hs) } constr(H)`,
	 `absurd : { hyp_list(Hs) } ident(H)`

- in `topology.v`:
  + lemma `filter_bigI_within`
  + lemma `near_powerset_map`
  + lemma `near_powerset_map_monoE`
  + lemma `fst_open`
  + lemma `snd_open`
  + definition `near_covering_within`
  + lemma `near_covering_withinP`
  + lemma `compact_setM`
  + lemma `compact_regular`
  + lemma `fam_compact_nbhs`
  + definition `compact_open`, notation `{compact-open, U -> V}`
  + notation `{compact-open, F --> f}`
  + definition `compact_openK`
  + definition `compact_openK_nbhs`
  + instance `compact_openK_nbhs_filter`
  + definition `compact_openK_topological_mixin`
  + canonicals `compact_openK_filter`, `compact_openK_topological`,
	`compact_open_pointedType`
  + definition `compact_open_topologicalType`
  + canonicals `compact_open_filtered`, `compact_open_topological`
  + lemma `compact_open_cvgP`
  + lemma `compact_open_open`
  + lemma `compact_closedI`
  + lemma `compact_open_fam_compactP`
  + lemma `compact_equicontinuous`
  + lemma `uniform_regular`
  + lemma `continuous_curry`
  + lemma `continuous_uncurry_regular`
  + lemma `continuous_uncurry`
  + lemma `curry_continuous`
  + lemma `uncurry_continuous`

### Changed

- in `topology.v`:
  + lemmas `nbhsx_ballx` and `near_ball` take a parameter of type `R` instead of `{posnum R}`
  + lemma `pointwise_compact_cvg`

### Renamed

### Generalized

- in `realfun.v`:
  + lemmas `nonincreasing_at_right_cvgr`, `nonincreasing_at_left_cvgr`
  + lemmas `nondecreasing_at_right_cvge`, `nondecreasing_at_right_is_cvge`,
    `nonincreasing_at_right_cvge`, `nonincreasing_at_right_is_cvge`

- in `realfun.v`:
  + lemmas `nonincreasing_at_right_is_cvgr`, `nondecreasing_at_right_is_cvgr`

### Deprecated

### Removed

### Infrastructure

### Misc
