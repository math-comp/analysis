# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`
  + lemma `in1_mksetP`

- in `topology_structure.v`
  + lemmas `open_bigcup_basis`, `continuous_on_basis`

- in `num_normedtype.v`
  + definition `itvoo_basis`
  + lemma `itvoo_basis_is_basis`

- in `lebesgue_integrable.v`
  + lemma `compact_continuous_Rintegrable`

- in `lebesgue_Rintegral.v`
  + lemmas `Rintegral_gt0`, `Rintegral_gt0_itvcc`

- in `exp.v`:
  + lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `ge0_lt1_powR_cvg0`, 
    `pownMexpR_cvgr0`, `powRMexpR_cvgr0`, `pownMpowR_cvgr0`,
    `pownMexpr_cvgn0`
  + instance `is_derive1_powRl`

- in `filter.v`:
  + type `filter_display`
  + definition `with_fdisp`
- in `discrete_topology.v`:
  + definition `discrete_display`
- in `function_spaces.v`:
  + definitions `ptws_display`, `arrow_uniform_display`, `uniform_display`, `uniform_fam_display`, `compact_open_display`
- in `initial_topology.v`:
  + definition `initial_display`
- in `one_point_compactification.v`:
  + definition `opc_display`
- in `order_topology.v`:
  + definition `order_display`
- in `quotient_topology.v`:
  + definition `quotient_display`
- in `subspace_topology.v`:
  + definition `subspace_display`
- in `subtype_topology.v`:
  + definition `set_type_topology_def`
- in `sup_topology.v`:
  + definition `supremum_display`
- in `tvs.v`:
  + definition `seminorm_display`

- in `separation_axioms.v`:
  + lemma `separated_set1`

- in `metric_structure.v`:
  + lemma `ball_open`
  + lemma `ball_open_nbhs`
  + lemma `metric_accessible`

- in `realfun.v`:
  + lemma `nondecreasing_discontinuity`

- new subdirectory `number_theory`
  + new file `number.v`
- in `realsum.v`:
  + lemma `esum_summableP`

- in `esum.v`:
  + lemma `fsetsTE`
- in `ftc.v`:
  + lemma `ge0_integration_by_substitution_shift_itvy`,
    `ge0_integration_by_substitution_shift_itvNy`
- in `derive.v`:
  + lemmas `derivable_row_mx`, `derive_row_mx`
  + instance `is_derive_row_mx`

- in `matrix_normedtype.v`
  + lemmas `norm_row_mx`, `norm_row_mx0r`, `norm_row_mx0l`, `cvg_row_mx`

- in `unstable.v`:
  + lemma `sub_row_mx`

- in `derive.v`:
  + lemmas `eqo_row_mx`, `drow_mx`, `diff_row_mx`,
    `differentiable_row_mx`
  + instance `is_diff_row_mx`

- in `functions.v`:
  + lemmas `zerofctE`, `onefctE`
- in `unstable.v`
  + lemmas `scalecE`, `normcr`, `Im_mul`, `mulrnc`, `complexA`, `normc_natmul`,
    `nomrc_mulrn`, `gt0_normc`, `gt0_realC`, `ltc0E`, `ltc0P`, `ltcP`, `lecP`,
    `realC_gt0`, `Creal_gtE`, `realC_norm`, `eqCr`, `eqCI`, `neqCr0`,
    `real_normc_ler`, `im_normc_ler`
  + notations `f %:Rfun`, `v %:Rc`
  + lemmas `realCZ`, `realC_alg`, `scalecr`, `scalecV`

- in `function_spaces.v`
  + lemmas `cvg_big`, `continuous_big`

- file `holomorphy.v`
  + instance of `normedModType` on `complex`
  + definition `ball_Rcomplex`
  + lemmas `entourage_RcomplexE`, `normcZ`, `Rcomplex_findim`
  + instance of `normedVectType` on `complex`
  + definitions `holomorphic`, `Rdifferentiable`, `realC`, `CauchyRiemannEq`
  + lemmas `holomorphicP`, `continuous_realC`, `Rdiff1`, `Rdiffi`, `littleoCo`,
    `holo_differentiable`, `holo_CauchyRiemann`, `Diff_CR_holo`,
    `holomorphic_Rdiff`

- in `landau.v`
  + lemma `littleoE0`

- in `normed_module.v`
  + structure `normedVectType`
  + lemmas `dnbhs0_le`, `nbhs0_le`, `dnbrg0_lt`, `nbhs0_lt`
  + definition `pseudometric`
  + instance of `normedZmodType`, `pointedType` and `pseudoMetricType`
    on `pseudometric`
  + definitions `oo_norm`, `oo_space`,
  + instance of `normedModType` on `oo_space`
  + lemmas `oo_closed_ball_compact`, `equivalence_norms`,
    `linear_findim_continuous`

- in `num_topology.v`
  + instance of `pseudoMetricType` on `GRing.regular`

- in `uniform_structure`
  + lemma `within_continuous_withinNx`

- in `tvs.v`
  + lemmas `cvg_sum`, `sum_continuous`, `entourage_nbhsE`
  + instance of `UniformZmodule.type` on `GRing.regular`

### Changed

- in `functions.v`:
  + lemmas `linfunP`, `linfun_eqP`
  + instances of `SubLmodule` and `pointedType` on `{linear _->_ | _ }`

- in `tvs.v`:
  + structure `LinearContinuous`
  + factory `isLinearContinuous`
  + instance of `ChoiceType` on `{linear_continuous _ -> _ }`
  + instance of `LinearContinuous` with the composition of two functions of type `LinearContinuous`
  + instance of `LinearContinuous` with the sum of two functions of type `LinearContinuous`
  + instance of `LinearContinuous` with the scalar multiplication of a function of type
    `LinearContinuous`
  + instance of `Continuous` on \-f when f is of type `LinearContinuous`
  + instance of `SubModClosed` on `{linear_continuous _ -> _}`
  + instance of `SubLModule` on  `{linear_continuous _ -> _ }`
  + instance of `LinearContinuous` on the null function
  + notations `{linear_continuous _ -> _ | _ }` and `{linear_continuous _ -> _ }`
  + definitions `lcfun`, `lcfun_key`, `lcfunP`
  + lemmas `lcfun_eqP`, `null_fun_continuous`, `fun_cvgD`,
   `fun_cvgN`, `fun_cvgZ`, `fun_cvgZr`
  + lemmas `lcfun_continuous` and `lcfun_linear`

- new files `signed_measure.v` and `radon_nikodym.v`
  + with the contents of `charge.v` (deprecated)

- in `esum.v`:
  + lemma `ge0_esum`
  + lemma `esum_ge`

- in `functions.v`:
  + lemma `preimageD1`

- in `measure_function.v`:
  + lemmas `cvg_measure_bigcap`, `cvg_measure_bigcup`

- in `classical_sets.v`:
  + lemma `bigcup_bigsetU`

- in `measurable_structure.v`:
  + lemmas `countable_bigcap_measurable`, `countable_bigcup_measurable`

### Changed

- in `lebesgue_integral_nonneg.v`, generalized and deprecated:
  + lemma `ge0_integralZl_EFin` (no condition on `k`)
- in file `function_spaces.v`,
  + new lemma `within_continuous_big`.
- in `nat_topology.v`:
  + new lemma `near_infty_after`.
- in `num_topology.v`;
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`, 
    `at_left_shift`, `at_right_shift`
- in `realfun.v`:
  + lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`, 
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`,
    `derivable_oo_LRcontinuousS`

- in `filter.v`:
  + implicit arguments of `continuous_comp`

- in `pseudometric_normed_Zmodule.v`:
  + implicit arguments of `distm_lt_split`, `distm_lt_splitr`, `distm_lt_splitl`

- in `pseudometric_structure.v`:
  + implicit arguments of `ball_split`, `ball_splitr`, `ball_splitl`

- moved from `pseudometric_normed_Zmodule.v` to `num_topology.v`
  + lemma `ball_itv`

- moved from `theories` to `number_theory`:
  + files `pi_irrational.v`

- moved from `theories/showcase` to `number_theory`:
  + files `pnt.v`

### Renamed

- in `lebesgue_measure.v`:
  + `compact_finite_measure` -> `compact_lebesgue_measure_lty`

- in `pseudometric_normed_Zmodule.v`:
  + `ball_open` -> `pseudo_ball_open`
  + `ball_open_nbhs` -> `pseudo_ball_open_nbhs`

### Generalized

- in `lebesgue_integral_nonneg.v`:
  + lemmas `ge0_integralZl`, `ge0_integralZr`

### Deprecated

- in `realfun.v`:
  + lemma `nondecreasing_fun_sum_le`

### Removed

### Infrastructure

### Misc
