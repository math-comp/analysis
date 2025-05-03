# Changelog (unreleased)

## [Unreleased]

### Added

- in `unstable.v`:
  + lemma `sqrtK`

- in `realfun.v`:
  + instance `is_derive1_sqrt`
- in `mathcomp_extra.v`:
  + lemmas `subrKC`, `sumr_le0`, `card_fset_sum1`

- in `functions.v`:
  + lemmas `fct_prodE`, `prodrfctE`

- in `exp.v:
  + lemma `norm_expR`
- in `hoelder.v`
  + lemma `hoelder_conj_ge1`

- in `reals.v`:
  + definition `irrational`
  + lemmas `irrationalE`, `rationalP` 

- in `topology_structure.v`:
  + lemmas `denseI`, `dense0`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `dense_set1C`

- new file `borel_hierarchy.v`:
  + definitions `Gdelta`, `Fsigma`
  + lemmas `closed_Fsigma`, `Gdelta_measurable`, `Gdelta_subspace_open`,
    `irrational_Gdelta`, `not_rational_Gdelta`
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
- in `exp.v`
  + lemma `expR_ge1Dxn`
- in `classical_sets.v`
  + lemma `bigcup_mkord_ord`

- in `measure.v`:
  + definition `g_sigma_preimage`
  + lemma `g_sigma_preimage_comp`
  + definition `measure_tuple_display`
  + lemma `measurable_tnth`
  + lemma `measurable_fun_tnthP`
  + lemma `measurable_cons`
  + lemma `measurable_behead`

- in `lebesgue_integral_theory/lebesgue_integral_nonneg.v`:
  + lemmas `ge0_nondecreasing_set_nondecreasing_integral`,
           `ge0_nondecreasing_set_cvg_integral`,
           `le0_nondecreasing_set_nonincreasing_integral`,
	   `le0_nondecreasing_set_cvg_integral`
- in `exp.v`:
  + lemma `norm_expR`
  + lemmas `expeR_eqy`
  + lemmas `lt0_ln`
  + lemmas `lt0_powR`, `powR_eq1`
  + Section `Lne`
  + definition `lne`
  + lemmas `lne0`, `lne_EFin`, `expeRK`, `lneK`, `lneK_eq`, `lne1`, `lneM`, 
    `lne_inj`, `lneV`, `lne_div`, `ltr_lne`, `ler_lne`, `lneXn`, `le_lne1Dx`, 
    `lne_sublinear`, `lne_ge0`, `lne_lt0`, `lne_gt0`, `lne_le0_le0`

### Changed

- moved from `pi_irrational.v` to `reals.v` and changed
  + definition `rational`

### Renamed

- in `lebesgue_stieltjes_measure.v`:
  + `cumulativeNy0` -> `cumulativeNy`
  + `cumulativey1` -> `cumulativey`

### Generalized

- in `functions.v`
  + lemma `fct_sumE` (from a pointwise equality to a functional one)

### Deprecated

### Removed

- file `forms.v` (superseded by MathComp's `sesquilinear.v`)

### Infrastructure

### Misc
