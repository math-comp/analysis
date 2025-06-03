# Changelog (unreleased)

## [Unreleased]

### Added

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

- in `normed_module.v`:
  + definition `pseudoMetric_normed`
  + factory `Lmodule_isNormed`
- in `num_normedtype.v`:
  + lemmas `gt0_cvgMrNy`, `gt0_cvgMry`

- in `probability.v`:
  + definition `exponential_pdf`
  + lemmas `exponential_pdf_ge0`, `lt0_exponential_pdf`,
    `measurable_exponential_pdf`, `exponential_pdfE`,
    `in_continuous_exponential_pdf`, `within_continuous_exponential_pdf`
  + definition `exponential_prob`
  + lemmas `derive1_exponential_pdf`, `exponential_prob_itv0c`,
    `integral_exponential_pdf`, `integrable_exponential_pdf`

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

- in `derive.v`:
  + lemmas `is_deriveX`, `deriveX`, `exp_derive`, `exp_derive1`

### Deprecated

### Removed

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`

### Infrastructure

### Misc
