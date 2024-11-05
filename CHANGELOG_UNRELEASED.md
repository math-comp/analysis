# Changelog (unreleased)

## [Unreleased]

### Added

- in `num_topology.v`:
  + lemma `in_continuous_mksetP`

- in `normedtype.v`:
  + lemmas `continuous_within_itvcyP`, `continuous_within_itvNycP`

- in `mathcomp_extra.v`:
  + lemma `partition_disjoint_bigfcup`
- in `lebesgue_measure.v`:
  + lemma `measurable_indicP`
- in `constructive_ereal.v`:
  + notation `\prod_( i <- r | P ) F` for extended real numbers and its variants

- in `numfun.v`:
  + defintions `funrpos`, `funrneg` with notations `^\+` and `^\-`
  + lemmas `funrpos_ge0`, `funrneg_ge0`, `funrposN`, `funrnegN`, `ge0_funrposE`,
    `ge0_funrnegE`, `le0_funrposE`, `le0_funrnegE`, `ge0_funrposM`, `ge0_funrnegM`,
    `le0_funrposM`, `le0_funrnegM`, `funr_normr`, `funrposneg`, `funrD_Dpos`,
    `funrD_posD`, `funrpos_le`, `funrneg_le`
  + lemmas `funerpos`, `funerneg`

- in `measure.v`:
  + lemma `preimage_class_comp`
  + defintions `mapping_display`, `g_sigma_algebra_mappingType`, `g_sigma_algebra_mapping`,
    notations `.-mapping`, `.-mapping.-measurable`

- in `lebesgue_measure.v`:
  + lemma `measurable_indicP`
  + lemmas `measurable_funrpos`, `measurable_funrneg`

- in `lebesgue_integral.v`:
  + definition `dyadic_approx` (was `Let A`)
  + definition `integer_approx` (was `Let B`)
  + lemma `measurable_sum`
  + lemma `integrable_indic`

- in `constructive_ereal.v`:
  + notations `\prod` in scope ereal_scope
  + lemmas `prode_ge0`, `prode_fin_num`
- in `probability.v`:
  + lemma `expectation_def`
  + notation `'M_`
- in `probability.v`:
  + lemma `expectationM_ge0`
  + definition `independent_events`
  + definition `mutual_independence`
  + definition `independent_RVs`
  + definition `independent_RVs2`
  + lemmas `g_sigma_algebra_mapping_comp`, `g_sigma_algebra_mapping_funrpos`,
    `g_sigma_algebra_mapping_funrneg`
  + lemmas `independent_RVs2_comp`, `independent_RVs2_funrposneg`,
    `independent_RVs2_funrnegpos`, `independent_RVs2_funrnegneg`,
    `independent_RVs2_funrpospos`
  + lemma `expectationM_ge0`, `integrable_expectationM`, `independent_integrableM`,
    ` expectation_prod`

- in `lebesgue_integral.v`:
  + lemmas `integrable_pushforward`, `integral_pushforward`
  + lemma `integral_measure_add`

- in `probability.v`
  + lemma `integral_distribution` (existing lemma `integral_distribution` has been renamed)

- in `measure.v`:
  + lemma `countable_bigcupT_measurable`

- in file `realfun.v`:
  + lemma `cvg_nbhsP`

- in `lebesgue_measure.v`:
  + lemma `measurable_powRr`

- in `measure.v`:
  + definition `discrete_measurable`
  + lemmas `discrete_measurable0`, `discrete_measurableC`, `discrete_measurableU`

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`
  

- in file `normedtype.v`,
     changed `completely_regular_space` to depend on uniform separators
     which removes the dependency on `R`.  The old formulation can be
     recovered easily with `uniform_separatorP`.

- moved from `Rstruct.v` to `Rstruct_topology.v`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`,
    `continuity_ptE`, `continuity_pt_cvg'`, `continuity_pt_dnbhs`
    and `nbhs_pt_comp`

- moved from `real_interval.v` to `normedtype.v`
  + lemmas `set_itvK`, `RhullT`, `RhullK`, `set_itv_setT`,
    `Rhull_smallest`, `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`,
    `disj_itv_Rhull`
- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in `lebesgue_integral.v`:
  + structure `SimpleFun` now inside a module `HBSimple`
  + structure `NonNegSimpleFun` now inside a module `HBNNSimple`
  + lemma `cst_nnfun_subproof` has now a different statement
  + lemma `indic_nnfun_subproof` has now a different statement
- in `mathcomp_extra.v`:
  + definition `idempotent_fun`

- in `topology_structure.v`:
  + definitions `regopen`, `regclosed`
  + lemmas `closure_setC`, `interiorC`, `closureU`, `interiorU`,
           `closureEbigcap`, `interiorEbigcup`,
	   `closure_open_regclosed`, `interior_closed_regopen`,
	   `closure_interior_idem`, `interior_closure_idem`

- in file `topology_structure.v`,
  + mixin `isContinuous`, type `continuousType`, structure `Continuous`
  + new lemma `continuousEP`.
  + new definition `mkcts`.

- in file `subspace_topology.v`,
  + new lemmas `continuous_subspace_setT`, `nbhs_prodX_subspace_inE`, and
    `continuous_subspace_prodP`.
  + type `continuousFunType`, HB structure `ContinuousFun`

- in file `subtype_topology.v`,
  + new lemmas `subspace_subtypeP`, `subspace_sigL_continuousP`,
    `subspace_valL_continuousP'`, `subspace_valL_continuousP`, `sigT_of_setXK`,
    `setX_of_sigTK`, `setX_of_sigT_continuous`, and `sigT_of_setX_continuous`.

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`

### Changed

### Renamed

- in `lebesgue_measure.v`:
  + `measurable_fun_indic` -> `measurable_indic`
  + `emeasurable_fun_sum` -> `emeasurable_sum`
  + `emeasurable_fun_fsum` -> `emeasurable_fsum`
  + `ge0_emeasurable_fun_sum` -> `ge0_emeasurable_sum`
- in `probability.v`:
  + `expectationM` -> `expectationZl`

- in `classical_sets.v`:
  + `preimage_itv_o_infty` -> `preimage_itvoy`
  + `preimage_itv_c_infty` -> `preimage_itvcy`
  + `preimage_itv_infty_o` -> `preimage_itvNyo`
  + `preimage_itv_infty_c` -> `preimage_itvNyc`

- in `constructive_ereal.v`:
  + `maxeMr` -> `maxe_pMr`
  + `maxeMl` -> `maxe_pMl`
  + `mineMr` -> `mine_pMr`
  + `mineMl` -> `mine_pMl`

- in `probability.v`:
  + `integral_distribution` -> `ge0_integral_distribution`
  + `expectationM` -> `expectationMl`

- file `homotopy_theory/path.v` -> `homotopy_theory/continuous_path.v`

### Generalized

- in `sequences.v`:
  + lemmas `cvg_restrict`, `cvg_centern`, `cvg_shiftn cvg_shiftS`

- in `probability.v`:
  + definition `random_variable`
  + lemmas `notin_range_measure`, `probability_range`
  + definition `distribution`
  + lemma `probability_distribution`, `integral_distribution`
  + mixin `MeasurableFun_isDiscrete`
  + structure `discreteMeasurableFun`
  + definition `discrete_random_variable`
  + lemma `dRV_dom_enum`
  + definitions `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV`, `sum_enum_prob`

- in `lebesgue_integral.v`:
  + lemma `measurable_sfunP`

### Deprecated

- in file `lebesgue_integral.v`:
  + lemma `approximation`

### Removed

- in `topology_structure.v`:
  + lemma `closureC`

- in file `lebesgue_integral.v`:
  + lemma `approximation`

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

- in `lebesgue_integral.v`:
  + lemma `measurable_indic` (was uselessly specializing `measurable_fun_indic` (now `measurable_indic`) from `lebesgue_measure.v`)
  + notation `measurable_fun_indic` (deprecation since 0.6.3)
- in `constructive_ereal.v`
  + notation `lee_opp` (deprecated since 0.6.5)
  + notation `lte_opp` (deprecated since 0.6.5)
- in `measure.v`:
  + `dynkin_setI_bigsetI` (use `big_ind` instead)

- in `lebesgue_measurable.v`:
  + notation `measurable_fun_power_pos` (deprecated since 0.6.3)
  + notation `measurable_power_pos` (deprecated since 0.6.4)

### Infrastructure

### Misc
