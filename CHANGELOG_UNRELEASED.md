# Changelog (unreleased)

## [Unreleased]

### Added

- in file `cantor.v`,
  + new definitions `cantor_space`, `cantor_like`, `pointed_discrete`, and 
    `tree_of`.
  + new lemmas `cantor_space_compact`, `cantor_space_hausdorff`, 
    `cantor_zero_dimensional`, `cantor_perfect`, `cantor_like_cantor_space`, 
    `tree_map_props`, `homeomorphism_cantor_like`, and 
    `cantor_like_finite_prod`.
  + new theorem `cantor_surj`.
- in file `topology.v`,
  + new lemmas `perfect_set2`, and `ent_closure`.
  + lemma `clopen_surj`

- in `cantor.v`:
  + definitions `pointed_principal_filter`,
    `pointed_discrete_topology`
  + lemma `discrete_pointed`
  + lemma `discrete_bool_compact`
- in `normedtype.v`:
  + hints for `at_right_proper_filter` and `at_left_proper_filter`

- in `realfun.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`,
    `increasing_fun`, `decreasing_fun`
  + lemmas `cvg_addrl`, `cvg_addrr`, `cvg_centerr`, `cvg_shiftr`,
    `nondecreasing_cvgr`,
	`nonincreasing_at_right_cvgr`,
	`nondecreasing_at_right_cvgr`,
	`nondecreasing_cvge`, `nondecreasing_is_cvge`,
	`nondecreasing_at_right_cvge`, `nondecreasing_at_right_is_cvge`,
	`nonincreasing_at_right_cvge`, `nonincreasing_at_right_is_cvge`
- in `ereal.v`:
  + lemmas `ereal_sup_le`, `ereal_inf_le`

- in `normedtype.v`:
  + definition `lower_semicontinuous`
  + lemma `lower_semicontinuousP`

- in `numfun.v`:
  + lemma `patch_indic`

- in `lebesgue_measure.v`
  + lemma `lower_semicontinuous_measurable`

- in `lebesgue_integral.v`:
  + definition `locally_integrable`
  + lemmas `integrable_locally`, `locally_integrableN`, `locally_integrableD`,
    `locally_integrableB`
  + definition `iavg`
  + lemmas `iavg0`, `iavg_ge0`, `iavg_restrict`, `iavgD`
  + definitions `HL_maximal`
  + lemmas `HL_maximal_ge0`, `HL_maximalT_ge0`,
    `lower_semicontinuous_HL_maximal`, `measurable_HL_maximal`,
    `maximal_inequality`

- in file `measure.v`
  + add lemmas `ae_eq_subset`, `measure_dominates_ae_eq`.

- in `charge.v`
  + definition `charge_of_finite_measure` (instance of `charge`)
  + lemmas `dominates_cscalel`, `dominates_cscaler`
  + definition `cpushforward` (instance of `charge`)
  + lemma `dominates_pushforward`
  + lemma `cjordan_posE`
  + lemma `jordan_posE`
  + lemma `cjordan_negE`
  + lemma `jordan_negE`
  + lemma `Radon_Nikodym_sigma_finite`
  + lemma `Radon_Nikodym_fin_num`
  + lemma `Radon_Nikodym_integral`
  + lemma `ae_eq_Radon_Nikodym_SigmaFinite`
  + lemma `Radon_Nikodym_change_of_variables`
  + lemma `Radon_Nikodym_cscale`
  + lemma `Radon_Nikodym_cadd`
  + lemma `Radon_Nikodym_chain_rule`

- in `sequences.v`:
  + lemma `minr_cvg_0_cvg_0`
  + lemma `mine_cvg_0_cvg_fin_num`
  + lemma `mine_cvg_minr_cvg`
  + lemma `mine_cvg_0_cvg_0`
  + lemma `maxr_cvg_0_cvg_0`
  + lemma `maxe_cvg_0_cvg_fin_num`
  + lemma `maxe_cvg_maxr_cvg`
  + lemma `maxe_cvg_0_cvg_0`
- in `constructive_ereal.v`
  + lemma `lee_subgt0Pr`

- in `topology.v`:
  + lemma `nbhs_dnbhs_neq`

- in `normedtype.v`:
  + lemma `not_near_at_rightP`

- in `realfun.v`:
  + lemma `cvg_at_right_left_dnbhs`
  + lemma `cvg_at_rightP`
  + lemma `cvg_at_leftP`
  + lemma `cvge_at_rightP`
  + lemma `cvge_at_leftP`
  + lemma `lime_sup`
  + lemma `lime_inf`
  + lemma `lime_supE`
  + lemma `lime_infE`
  + lemma `lime_infN`
  + lemma `lime_supN`
  + lemma `lime_sup_ge0`
  + lemma `lime_inf_ge0`
  + lemma `lime_supD`
  + lemma `lime_sup_le`
  + lemma `lime_inf_sup`
  + lemma `lim_lime_inf`
  + lemma `lim_lime_sup`
  + lemma `lime_sup_inf_at_right`
  + lemma `lime_sup_inf_at_left`

- in `normedtype.v`:
  + lemmas `withinN`, `at_rightN`, `at_leftN`, `cvg_at_leftNP`, `cvg_at_rightNP`
  + lemma `dnbhsN`
  + lemma `limf_esup_dnbhsN`

- in `topology.v`:
  + lemma `dnbhs_ball`

- in `normedtype.v`
  + definitions `limf_esup`, `limf_einf`
  + lemmas `limf_esupE`, `limf_einfE`, `limf_esupN`, `limf_einfN`

- in `sequences.v`:
  + lemmas `limn_esup_lim`, `limn_einf_lim`

- in `realfun.v`:
  + lemmas `lime_sup_lim`, `lime_inf_lim`

- in `boolp.v`:
  + tactic `eqProp`
  + variant `BoolProp`
  + lemmas `PropB`, `notB`, `andB`, `orB`, `implyB`, `decide_or`, `not_andE`,
    `not_orE`, `orCA`, `orAC`, `orACA`, `orNp`, `orpN`, `or3E`, `or4E`, `andCA`,
	 `andAC`, `andACA`, `and3E`, `and4E`, `and5E`, `implyNp`, `implypN`,
	 `implyNN`, `or_andr`, `or_andl`, `and_orr`, `and_orl`, `exists2E`,
	 `inhabitedE`, `inhabited_witness`
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

- in `ereal.v`:
  + lemma `ereal_supy`

- in `mathcomp_extra.v`:
  + lemmas `last_filterP`,
    `path_lt_filter0`, `path_lt_filterT`, `path_lt_head`, `path_lt_last_filter`,
	`path_lt_le_last`

- in file `realfun.v`,
  + new definitions `itv_partition`, `itv_partitionL`, `itv_partitionR`, 
    `variation`, `variations`, `bounded_variation`, `total_variation`, 
    `neg_tv`, and `pos_tv`.

  + new lemmas `left_right_continuousP`,
    `nondecreasing_funN`, `nonincreasing_funN`

  + new lemmas `itv_partition_nil`, `itv_partition_cons`, `itv_partition1`,
    `itv_partition_size_neq0`, `itv_partitionxx`, `itv_partition_le`,
    `itv_partition_cat`, `itv_partition_nth_size`,
    `itv_partition_nth_ge`, `itv_partition_nth_le`, 
    `nondecreasing_fun_itv_partition`, `nonincreasing_fun_itv_partition`, 
    `itv_partitionLP`, `itv_partitionRP`, `in_itv_partition`, 
    `notin_itv_partition`, `itv_partition_rev`,

  + new lemmas `variation_zip`, `variation_prev`, `variation_next`, `variation_nil`,
    `variation_ge0`, `variationN`, `variation_le`, `nondecreasing_variation`, 
    `nonincreasing_variation`, `variationD`, `variation_itv_partitionLR`, 
    `le_variation`, `variation_opp_rev`, `variation_rev_opp`

  + new lemmas `variations_variation`, `variations_neq0`, `variationsN`, `variationsxx`

  + new lemmas `bounded_variationxx`, `bounded_variationD`, `bounded_variationN`,
    `bounded_variationl`, `bounded_variationr`, `variations_opp`, 
    `nondecreasing_bounded_variation`

  + new lemmas `total_variationxx`, `total_variation_ge`, `total_variation_ge0`,
    `bounded_variationP`, `nondecreasing_total_variation`, `total_variationN`,
	  `total_variation_le`, `total_variationD`, `neg_tv_nondecreasing`,
    `total_variation_pos_neg_tvE`, `fine_neg_tv_nondecreasing`,
    `neg_tv_bounded_variation`, `total_variation_right_continuous`,
    `neg_tv_right_continuous`, `total_variation_opp`,
    `total_variation_left_continuous`, `total_variation_continuous`

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
