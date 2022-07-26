# Changelog (unreleased)

## [Unreleased]

### Added
- in `normedtype.v`:
  + definitions `contraction` and `is_contraction`
  + lemma `contraction_fixpoint_unique`

- in `constructive_ereal.v`:
  + lemmas `ltNye_eq`, `sube_lt0`, `subre_lt0`, `suber_lt0`, `sube_ge0`
  + lemmas `dsubre_gt0`, `dsuber_gt0`, `dsube_gt0`, `dsube_le0`

- in `topology.v`:
  + lemma `near_inftyS`
  + lemma `continuous_closedP`, `closedU`, `pasting`

- in `sequences.v`:
  + lemmas `contraction_dist`, `contraction_cvg`,
    `contraction_cvg_fixed`, `banach_fixed_point`,
    `contraction_unique`
- in `mathcomp_extra.v`:
  + defintion `onem` and notation ``` `1- ```
  + lemmas `onem0`, `onem1`, `onemK`, `onem_gt0`, `onem_ge0`, `onem_le1`, `onem_lt1`,
    `onemX_ge0`, `onemX_lt1`, `onemD`, `onemMr`, `onemM`
- in `signed.v`:
  + lemmas `onem_PosNum`, `onemX_NngNum`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_fine`
- in `lebesgue_integral.v`:
  + lemma `ge0_integral_mscale`
- in `measure.v`:
  + lemma `measurable_funTS`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_indic`
  + lemma `big_const_idem`
  + lemma `big_id_idem`
  + lemma `big_rem_AC`
  + lemma `bigD1_AC`
  + lemma `big_mkcond_idem`
  + lemma `big_split_idem`
  + lemma `big_id_idem_AC`
  + lemma `bigID_idem`
- in `mathcomp_extra.v`:
  + lemmas `bigmax_le` and `bigmax_lt`
  + lemma `bigmin_idr`
  + lemma `bigmax_idr`
- in `classical_sets.v`:
  + lemma `subset_refl`
- in `fsbigop.v`:
  + lemma `lee_fsum_nneg_subset`

### Changed

- in `measure.v`:
  + generalize `measurable_uncurry`
  + generalize `pushforward`
- in `lebesgue_integral.v`
  + change `Arguments` of `eq_integrable`
- in `lebesgue_integral.v`:
  + fix pretty-printing of `{mfun _ >-> _}`, `{sfun _ >-> _}`, `{nnfun _ >-> _}`
- in `lebesgue_integral.v`
  + minor generalization of `eq_measure_integral`
- from `topology.v` to `mathcomp_extra.v`:
  + generalize `ltr_bigminr` to `porderType` and rename to `bigmin_lt`
  + generalize `bigminr_ler` to `orderType` and rename to `bigmin_le`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v` and generalized to `orderType`:
  + lemma `bigminr_ler_cond`, renamed to `bigmin_le_cond`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v`:
  + lemma `bigminr_maxr`
- moved from from module `Bigminr` in `normedtype.v`
  + to `mathcomp_extra.v` and generalized to `orderType`
    * `bigminr_mkcond` -> `bigmin_mkcond`
    * `bigminr_split` -> `bigmin_split`
    * `bigminr_idl` -> `bigmin_idl`
    * `bigminrID` -> `bigminID`
    * `bigminrD1` -> `bigminD1`
    * `bigminr_inf` -> `bigmin_inf`
    * `bigminr_gerP` -> `bigmin_geP`
    * `bigminr_gtrP` -> ``bigmin_gtP``
    * `bigminr_eq_arg` -> `bigmin_eq_arg`
    * `eq_bigminr` -> `eq_bigmin`
  + to `topology.v` and generalized to `orderType`
    * `bigminr_lerP` -> `bigmin_leP`
    * `bigminr_ltrP` -> `bigmin_ltP`
- moved from `topology.v` to `mathcomp_extra.v`:
  + `bigmax_lerP` -> `bigmax_leP`
  + `bigmax_ltrP` -> `bigmax_ltP`
  + `ler_bigmax_cond` -> `le_bigmax_cond`
  + `ler_bigmax` -> `le_bigmax`
  + `le_bigmax` -> `homo_le_bigmax`
- in `esum.v`:
  + definition `esum`

### Renamed

- in `constructive_ereal.v`:
  + `lte_pinfty_eq` -> `ltey_eq`
- in `sequences.v`:
  + `nneseries_lim_ge0` -> `nneseries_ge0`
- in `constructive_ereal.v`:
  + `le0R` -> `fine_ge0`
  + `lt0R` -> `fine_gt0`
- in `measure.v`:
  + `ring_fsets` -> `ring_finite_set`
  + `discrete_measurable` -> `discrete_measurable_nat`
- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `measure.v`:
  + `cvg_mu_inc` -> `nondecreasing_cvg_mu`
- in `lebesgue_integral.v`:
  + `muleindic_ge0` -> `nnfun_muleindic_ge0`
  + `mulem_ge0` -> `mulemu_ge0`
  + `nnfun_mulem_ge0` -> `nnsfun_mulemu_ge0`

### Removed

- in `normedtype.v` (module `Bigminr`)
  + `bigminr_ler_cond`, `bigminr_ler`.
  + `bigminr_seq1`, `bigminr_pred1_eq`, `bigminr_pred1`
- in `topology.v`:
  + `bigmax_seq1`, `bigmax_pred1_eq`, `bigmax_pred1`
- in `esum.v`:
  + lemma `fsetsP`, `sum_fset_set`

### Infrastructure

### Misc
