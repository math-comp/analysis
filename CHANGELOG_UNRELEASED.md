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
- in file `normedtype.v`,
  + new lemma `continuous_within_itvP`.

- in file `realfun.v`,
  + new definitions `itv_partition`, `itv_partitionL`, `itv_partitionR`, 
    `variation`, `variations`, `bounded_variation`, `total_variation`, 
    `neg_tv`, and `pos_tv`.

  + new lemmas `left_right_continuousP`, `nondecreasing_funN`, 
    `nonincreasing_funN`, `has_ubound_ereal_sup`, `sup_le`, `ereal_supy`, 
    `path_lt_filter0`, `path_lt_filterT`, `last_filter_lt`, `last_filter`, 
    `path_inv`, `path_lt_le_last`, `itv_partition_nil`, `itv_partition1`, 
    `itv_partition_cons`, `itv_partitionxx`, `itv_partition_le`, 
    `itv_partition_tail`, `itv_partition_cat`, `itv_partition_nth_size`, 
    `itv_partition_nth_ge`, `itv_partition_nth_le`, 
    `nondecreasing_fun_itv_partition`, `nonincreasing_fun_itv_partition`, 
    `itv_partitionLP`, `itv_partitionRP`, `in_itv_partition`, 
    `notin_itv_partition`, `itv_partition_rev`, `variationE`, `variation_nil`, 
    `variation_ge0`, `variationN`, `variation_le`, `nondecreasing_variation`, 
    `nonincreasing_variation`, `variationD`, `variation_itv_partitionLR`, 
    `le_variation`, `variation_opp_rev`, `variation_rev_opp`, 
    `variations_variation`, `variations_neq0`, `variationsN`, `variationsxx`, 
    `bounded_variationxx`, `bounded_variationD`, `bounded_variationN`, 
    `bounded_variationl`, `bounded_variationr`, `variations_opp`, 
    `nondecreasing_bounded_variation`, `total_variationxx`, 
    `total_variation_ge`, `total_variation_ge0`, 
    `nondecreasing_total_variation`, `bounded_variationP`, `total_variationN`, 
    `total_variation_le`, `total_variationD`, `neg_TV_increasing`, 
    `total_variation_jordan_decompE`, `neg_TV_increasing_fin`, 
    `neg_TV_bounded_variation`, `TV_right_continuous`, 
    `neg_TV_right_continuous`, `total_variation_opp`, `TV_left_continuous`, and 
    `TV_continuous`.

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
