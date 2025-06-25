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

- in `exp.v`:
  + lemmas `expeR_eqy`
  + lemmas `lt0_powR1`, `powR_eq1`
  + definition `lne`
  + lemmas `lne0`, `lne_EFin`, `expeRK`, `lneK`, `lneK_eq`, `lne1`, `lneM`, 
    `lne_inj`, `lneV`, `lne_div`, `lte_lne`, `lee_lne`, `lneXn`, `le_lne1Dx`, 
    `lne_sublinear`, `lne_ge0`, `lne_lt0`, `lne_gt0`, `le1_lne_le0`

- in `constructive_ereal.v`:
  + lemma `expe0`, `mule0n`, `muleS`

### Changed

- moved from `pi_irrational.v` to `reals.v` and changed
  + definition `rational`
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

- in `simple_functions.v`:
  + lemma `mfunMn`

- in `hoelder.v`
  + lemmas `Lnorm0`, `Lnorm_cst1`
  + definition `hoelder_conjugate`
  + lemmas `hoelder_conjugate0`, `hoelder_conjugate1`, `hoelder_conjugate2`,
    `hoelder_conjugatey`, `hoelder_conjugateK`
  + lemmas `lerB_DLnorm`, `lerB_LnormD`, `eminkowski`
  + definition `finite_norm`
  + mixin `isLfunction` with field `Lfunction_finite`
  + structure `Lfunction`
  + notation `LfunType`
  + definition `Lequiv`
  + canonical `Lequiv_canonical`
  + definition `LspaceType`
  + lemma `LequivP`
  + record `LType`
  + coercion `LfunType_of_LType`
  + definition `Lspace` with notation `mu.-Lspace p`
  + lemma `Lfun_integrable`, `Lfun1_integrable`, `Lfun2_integrable_sqr`, `Lfun2_mul_Lfun1`
  + lemma `Lfun_scale`, `Lfun_cst`,
  + definitions `finLfun`, `Lfun`, `Lfun_key`
  + canonical `Lfun_keyed`
  + lemmas `sub_Lfun_mfun`, `sub_Lfun_finLfun`
  + definition `Lfun_Sub`
  + lemmas `Lfun_rect`, `Lfun_valP`, `LfuneqP`, `finite_norm_cst0`, `mfunP`, `LfunP`,
    `mfun_scaler_closed`
  + lemmas `LnormZ`, `Lfun_submod_closed`
  + lemmas `finite_norm_fine`, `ler_LnormD`,
    `LnormrN`, `fine_Lnormr_eq0`
  + lemma `fine_Lnormr_eq0`
  + lemma `Lfun_subset`, `Lfun_subset12`
  + lemma `Lfun_oppr_closed`
  + lemma `Lfun_addr_closed`
  + lemmas `poweR_Lnorm`, `oppe_Lnorm`
  + lemma `integrable_poweR`

- in `hoelder.v`:
  + lemmas `hoelder_conjugate_div`, `hoelder_div_conjugate`,
    `hoelder_Mconjugate`, `hoelder_conjugateP`,
    `hoelder_conjugate_eq1`, `hoelder_conjugate_eqNy`, `hoelder_conjugate_eqy`,
    `hoelder_conjugateNy`

- in `constructive_ereal.v`:
  + lemma `expe0`, `mule0n`, `muleS`

### Changed

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
