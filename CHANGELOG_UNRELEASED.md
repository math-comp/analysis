# Changelog (unreleased)

## [Unreleased]

### Added
- in `measure.v`:
  + lemma `lebesgue_regularity_outer`

- in `lebesgue_measure.v`:
  + lemma `closed_measurable`

- in file `lebesgue_measure.v`,
  + new lemmas `lebesgue_nearly_bounded`, and `lebesgue_regularity_inner`.
- in file `measure.v`,
  + new lemmas `measureU0`, `nonincreasing_cvg_mu`, and `epsilon_trick0`.
- in file `real_interval.v`,
  + new lemma `bigcup_itvT`.
- in file `topology.v`,
  + new lemma `uniform_nbhsT`.

- in file `topology.v`,
  + new definitions `basis`, and `second_countable`.
  + new lemmas `clopen_countable` and `compact_countable_base`.
- in `classical_sets.v`:
  + lemmas `set_eq_le`, `set_neq_lt`,
  + new lemma `trivIset1`.
- in `set_interval.v`:
  + lemma `set_lte_bigcup`
- in `lebesgue_integral.v`:
  + lemmas `emeasurable_fun_lt`, `emeasurable_fun_le`, `emeasurable_fun_eq`,
    `emeasurable_fun_neq`
  + lemma `integral_ae_eq`
- in file `kernel.v`,
  + new definitions `kseries`, `measure_fam_uub`, `kzero`, `kdirac`,
    `prob_pointed`, `mset`, `pset`, `pprobability`, `kprobability`, `kadd`,
    `mnormalize`, `knormalize`, `kcomp`, and `mkcomp`.
  + new lemmas `eq_kernel`, `measurable_fun_kseries`, `integral_kseries`,
    `measure_fam_uubP`, `eq_sfkernel`, `kzero_uub`,
    `sfinite_kernel`, `sfinite_kernel_measure`, `finite_kernel_measure`,
    `measurable_prod_subset_xsection_kernel`,
    `measurable_fun_xsection_finite_kernel`,
    `measurable_fun_xsection_integral`,
    `measurable_fun_integral_finite_kernel`,
    `measurable_fun_integral_sfinite_kernel`, `lt0_mset`, `gt1_mset`,
    `kernel_measurable_eq_cst`, `kernel_measurable_neq_cst`, `kernel_measurable_fun_eq_cst`,
    `measurable_fun_kcomp_finite`, `mkcomp_sfinite`,
    `measurable_fun_mkcomp_sfinite`, `measurable_fun_preimage_integral`,
    `measurable_fun_integral_kernel`, and `integral_kcomp`.
  + lemma `measurable_fun_mnormalize`
- in `ereal.v`:
  + lemmas `compreDr`, `compreN`
- in `constructive_ereal.v`:
  + lemmas `lee_sqr`, `lte_sqr`, `lee_sqrE`, `lte_sqrE`, `sqre_ge0`,
    `EFin_expe`, `sqreD`, `sqredD`
- in `probability.v`
  + definition of `covariance`
  + lemmas `expectation_sum`, `covarianceE`, `covarianceC`,
    `covariance_fin_num`, `covariance_cst_l`, `covariance_cst_r`,
    `covarianceZl`, `covarianceZr`, `covarianceNl`, `covarianceNr`,
    `covarianceNN`, `covarianceDl`, `covarianceDr`, `covarianceBl`,
    `covarianceBr`, `variance_fin_num`, `varianceZ`, `varianceN`,
    `varianceD`, `varianceB`, `varianceD_cst_l`, `varianceD_cst_r`,
    `varianceB_cst_l`, `varianceB_cst_r`
- in `functions.v`:
  + lemma `sumrfctE`
- in `lebesgue_integral.v`:
  + lemma `integrable_sum`
- in `probability.v`
  + lemma `cantelli`
- in `classical_sets.v`:
  + lemmas `preimage_mem_true`, `preimage_mem_false`
- in `measure.v`:
  + definition `measure_dominates`, notation `` `<< ``
  + lemma `measure_dominates_trans`
- in `measure.v`:
  + defintion `mfrestr`
- in `charge.v`:
  + definition `measure_of_charge`
  + definition `crestr0`
  + definitions `jordan_neg`, `jordan_pos`
  + lemmas `jordan_decomp`, `jordan_pos_dominates`, `jordan_neg_dominates`
  + lemma `radon_nikodym_finite`
  + definition `Radon_Nikodym`, notation `'d nu '/d mu`
  + theorems `Radon_Nikodym_integrable`, `Radon_Nikodym_integral`

- in `measure.v`:
  + lemmas `measurable_pair1`, `measurable_pair2`
  + lemma `covariance_le`
- in `mathcomp_extra.v`
  + definition `coefE` (will be in MC 2.1/1.18)
  + lemmas `deg2_poly_canonical`, `deg2_poly_factor`, `deg2_poly_min`,
    `deg2_poly_minE`, `deg2_poly_ge0`, `Real.deg2_poly_factor`,
    `deg_le2_poly_delta_ge0`, `deg_le2_poly_ge0`
    (will be in MC 2.1/1.18)
  + lemma `deg_le2_ge0`
  + new lemmas `measurable_subring`, and `semiring_sigma_additive`.
  + added factory `Content_SubSigmaAdditive_isMeasure`

- in `lebesgue_integral.v`:
  + lemmas `integrableP`, `measurable_int`
- in file `topology.v`,
  + new definition `set_nbhs`, `smallest_filter_stage`.
  + new lemmas `smallest_filter_stage_sub`, `smallest_filter_stageP`, 
    `smallest_filter_finI`, and `set_nbhsP`.

### Changed

- moved from `lebesgue_measure.v` to `real_interval.v`:
  + lemmas `set1_bigcap_oc`, `itv_bnd_open_bigcup`, `itv_open_bnd_bigcup`,
    `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`
- in `lebesgue_measure.v`
  + `measurable_funrM`, `measurable_funN`, `measurable_fun_exprn`
- in `lebesgue_integral.v`:
  + lemma `xsection_ndseq_closed` generalized from a measure to a family of measures
  + locked `integrable` and put it in bool rather than Prop
- in `probability.v`
  + `variance` is now defined based on `covariance` 

- moved `subsetP` from `functions.v` to `classical_sets.v`
  + new definition `set_nbhs`.
  + new lemmas `smallest_filter_stage_sub`, `smallest_filter_stageE`, 
    `finI_fromI`, `smallest_filter_stage_finI`, `smallest_filter_finI`, and 
    `set_nbhsP`.

### Changed

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
