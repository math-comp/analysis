# Changelog (unreleased)

## [Unreleased]

### Added

- in new file `gauss_integral_alternative`
  + add lemmas `integral0y_gauss_fin_num`,
               `integral0y_u0`,
	       `integrable0y_u`,
	       `max_y_ge0`,
	       `u_dominates`,
	       `int0yu_fin_num`,
	       `cvgy_int0yu0`,
	       `dint0yuE`,
	       `derivable_int0yu`,
	       `rc_int0yu0`,
	       `gauss_integration`
- in `probability.v`:
  + lemmas `eq_bernoulli`, `eq_bernoulliV2`

- in `measure.v`:
  + lemmas `mnormalize_id`, `measurable_fun_eqP`

- in `ftc.v`:
  + lemma `integrable_locally`

- in `constructive_ereal.v`:
  + lemma `EFin_bigmax`

- in `mathcomp_extra.v`:
  + lemmas `inr_inj`, `inl_inj`

- in `classical_sets.v`:
  + lemmas `in_set1`, `inr_in_set_inr`, `inl_in_set_inr`, `mem_image`, `mem_range`, `image_f`
  + lemmas `inr_in_set_inl`, `inl_in_set_inl`

- in `lebesgue_integral_approximation.v` (now `measurable_fun_approximation.v`):
  + lemma `measurable_prod`
  + lemma `measurable_fun_lte`
  + lemma `measurable_fun_lee`
  + lemma `measurable_fun_eqe`
  + lemma `measurable_poweR`

- in `exp.v`:
  + lemma `poweRE`

- in `exp.v`:
  + lemmas `lnNy`, `powR_cvg0`, `derivable_powR`, `powR_derive1`
  + Instance `is_derive1_powR`
- in `realfun.v`:
  + lemma `cvge_ninftyP`

- in `boolp.v`:
  + lemmas `orW`, `or3W`, `or4W`
  
- in `classical_sets.v`:
  + lemmas `set_cst`, `image_nonempty`

- in `unstable.v`:
  + lemmas `eq_exists2l`, `eq_exists2r`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`
- in `functions.v`:
  + lemma `natmulfctE`

- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`
- in `constructive_ereal.v`:
  + lemmas `expe_ge0`, `expe_eq0`, `expe_gt0`

- in `ereal.v`:
  + lemmas `ereal_sup_cst`, `ereal_inf_cst`,
    `ereal_sup_pZl`, `ereal_supZl`, `ereal_inf_pZl`, `ereal_infZl`

- in `sequences.v`:
  + lemmas `ereal_inf_seq`, `ereal_sup_seq`
- in `unstable.v`:
  + lemma `subrKC`

- in `convex.v`:
  + definition `convex_quasi_associative`
    * implemented through a module `ConvexQuasiAssoc` containing
      `law` and helper lemmas
  + lemmas `convR_itv`, `convR_line_path`
- in `num_topology.v`
  + `topologicalType` instance on `R^o` for `R : numDomainType`

- in `tvs.v`
  + HB classes `TopologicalNmodule`, `TopologicalZmodule`, `TopologicalLmodule`
    `UniformNmodule`, `UniformZmodule`, `UniformLmodule`
  + notation `topologicalZmodType`
  + mixin `PreTopologicalNmodule_isTopologicalNmodule`,
    `TopologicalNmodule_isTopologicalZmodule`,
    `TopologicalZmodule_isTopologicalLmodule`,
    `PreUniformNmodule_isUniformNmodule`,
    `UniformNmodule_isUniformZmodule`,
    `PreUniformLmodule_isUniformLmodule`
  + structure `topologicalLmodule`
  + factories `PreTopologicalNmodule_isTopologicalZmodule`,
    `TopologicalNmodule_isTopologicalLmodule`,
    `PreUniformNmodule_isUniformZmodule`,
    `UniformNmodule_isUniformLmodule`
  + lemmas `sub_continuous`, `sub_unif_continuous`

- in `constructive_ereal.v`:
  + `inve` a total involutive inversion function on `\bar R`, denoted `^-1` in
     the `ereal_scope` coinciding with `x^-1%R` when `x != 0` but such that
     `0^-1 = +oo` and `-oo^-1 = -oo`,
  + notation `x / y` in `ereal_scope` for `x / y = x * y^-1`,
  + lemmas `inver`, `inveP`, `fine_invr`, `inve0`, `inve1`, `invey`, `invey`,
    `inveNy`, `inveK`, `invr_inj`, `inveN`, `inve_eq0`, `inve_ge0`, `inve_gt0`,
    `inv_gt0P`, `inve_lt0`, `inve_le0`, `inve_le0P`,
  + predicate `inveM_def` with notation `x *^-1? y` defining a sufficient
    condition for the inverse and product to commute, with lemmas `inveMP`,
    `inveM_defE`, `inveM` and `fin_inveM_def`,
  + compatibility lemma `mule_defE` to bridge the former definition of
    `mule_def` with the new one.
  + lemma `fin_numV`
  + lemmas `mulVe`, `lee_pV2`, `lte_pV2`, `ltee_pV2`, `inve_pge`, `inve_pgt`,
    `inve_ple`, `inve_plt`, `inve_gt1`, `inve_ge1`.

- in `lebesgue_integral_differentiation.v`:
  + lemma `nicely_shrinking_fin_num`

### Changed

- in `convex.v`:
  + convex combination operator `a <| t |> b` changed from
    `(1-t)a + tb` to `ta + (1-t)b`

- in `sequences.v`:
  + lemma `subset_seqDU`

- in `measure.v`:
  + lemmas `seqDU_measurable`, `measure_gt0`
  + notations `\forall x \ae mu, P`, `f = g %[ae mu in D]`, `f = g %[ae mu]`
  + instances `ae_eq_equiv`, `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
  + lemma `ae_eq_comp2`
  + lemma `ae_foralln`
  + lemma `ae_eqe_mul2l`

- new file `ess_sup_inf.v`:
  + lemma `measure0_ae`
  + definition `ess_esup`
  + lemmas `ess_supEae`, `ae_le_measureP`, `ess_supEmu0`, `ess_sup_ge`,
    `ess_supP`, `le_ess_sup`, `eq_ess_sup`, `ess_sup_cst`, `ess_sup_ae_cst`,
    `ess_sup_gee`, `abs_sup_eq0_ae_eq`, `abs_ess_sup_eq0`, `ess_sup_pZl`,
    `ess_supZl`, `ess_sup_eqNyP`, `ess_supD`, `ess_sup_absD`
  + notation `ess_supr`
  + lemmas `ess_supr_bounded`, `ess_sup_eqr0_ae_eq`, `ess_suprZl`,
    `ess_sup_ger`, `ess_sup_ler`, `ess_sup_cstr`, `ess_suprD`, `ess_sup_normD`
  + definition `ess_inf`
  + lemmas `ess_infEae`, `ess_infEN`, `ess_supEN`, `ess_infN`, `ess_supN`,
    `ess_infP`, `ess_inf_le`, `le_ess_inf`, `eq_ess_inf`, `ess_inf_cst`,
    `ess_inf_ae_cst`, `ess_inf_gee`, `ess_inf_pZl`, `ess_infZl`, `ess_inf_eqyP`,
    `ess_infD`
  + notation `ess_infr`
  + lemmas `ess_infr_bounded`, `ess_infrZl`, `ess_inf_ger`, `ess_inf_ler`,
    `ess_inf_cstr`

- in `measure.v`:
  + notation `{ae mu, P}` (near use `{near _, _}` notation)
  + definition `ae_eq`
  + `ae_eq` lemmas now for `ringType`-valued functions (instead of `\bar R`)

- in `convex.v`:
  + definition `convex_realDomainType` generalized and
    renamed accordingly `convex_numDomainType`
- in `tvs.v`
  + HB class `UniformZmodule` now contains `TopologicalZmodule`
  + HB class `UniformLmodule` now contains `TopologicalLmodule`

- in `constructive_ereal.v`:
  + `mule` has special cases optimizing computation for +oo and -oo
  + `mule_def` has been rewritten to optimize computation in several cases.

- in `lebesgue_integral_nonneg.v`:
  + lemma `integral_abs_eq0` (remove redundant hypotheses)

- in `lebesgue_integral_differentiation.v`:
  + definition `iavg` (to use `inve`)

### Renamed

- in `measure.v`
  + definition `ess_sup` moved to `ess_sup_inf.v`

- in `convex.v`
  + lemma `conv_gt0` to `convR_gt0`
- in `tvs.v`
  + HB class `TopologicalNmodule` moved to `PreTopologicalNmodule`
  + HB class `TopologicalZmodule` moved to `PreTopologicalZmodule`
  + HB class `TopologicalLmodule` moved to `PreTopologicalLmodule`
  + structure `topologicalLmodule` moved to `preTopologicalLmodule`
  + HB class `UniformNmodule` moved to `PreUniformNmodule`
  + HB class `UniformZmodule` moved to `PreUniformZmodule`
  + HB class `UniformLmodule` moved to `PreUniformLmodule`


### Generalized

- in `derive.v`:
  + `derive_cst`, `derive1_cst`
- in `convex.v`
  + parameter `R` of `convType` from `realDomainType` to `numDomainType`

### Deprecated

### Removed

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`

### Infrastructure

### Misc
