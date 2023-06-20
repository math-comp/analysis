# Changelog (unreleased)

## [Unreleased]

### Added

- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `topology.v`:
  + lemma `globally0`
- in `normedtype.v`:
  + lemma `lipschitz_set0`, `lipschitz_set1`
- in `measure.v`:
  + lemma `measurable_fun_bigcup`
- in `sequences.v`:
  + lemma `eq_eseriesl`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`

- in `lebesgue_measure.v`:
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`
- in `convex.v`:
  + lemmas `conv_gt0`, `convRE`

- in `exp.v`:
  + lemmas `concave_ln`, `conjugate_powR`

- in file `lebesgue_integral.v`,
  + new lemmas `integral_le_bound`, `continuous_compact_integrable`, and 
    `lebesgue_differentiation_continuous`.

- in `normedtype.v`:
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`

- in `lebesgue_measure.v`:
  + lemma `measurable_ball`

- in file `normedtype.v`,
  + new lemmas `normal_openP`, `uniform_regular`,
    `regular_openP`, and `pseudometric_normal`.
- in file `topology.v`,
  + new definition `regular_space`.
  + new lemma `ent_closure`.

- in file `lebesgue_integral.v`,
  + new lemmas `simple_bounded`, `measurable_bounded_integrable`, 
    `compact_finite_measure`, `approximation_continuous_integrable`

- in `sequences.v`:
  + lemma `cvge_harmonic`

- in `mathcomp_extra.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq`

- in `constructive_ereal.v`:
  + lemma `bigmaxe_fin_num`
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

- in file `cantor.v`,
  + new definitions `cantor_space`, `cantor_like`, `pointedDiscrete`, and 
    `tree_of`.
  + new lemmas `cantor_space_compact`, `cantor_space_hausdorff`, 
    `cantor_zero_dimensional`, `cantor_perfect`, `cantor_like_cantor_space`, 
    `tree_map_props`, `homeomorphism_cantor_like`, and 
    `cantor_like_finite_prod`.
  + new theorem `cantor_surj`.
- in file `topology.v`,
  + new lemmas `perfect_set2`, and `ent_closure`.

### Changed
  
### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
