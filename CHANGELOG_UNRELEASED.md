# Changelog (unreleased)

## [Unreleased]

### Added

- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`

- in `lebesgue_measure.v`:
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`
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
  + new definition `set_nbhs`.
  + new lemmas `filterI_iter_sub`, `filterI_iterE`, `finI_fromI`, 
    `filterI_iter_finI`, `smallest_filter_finI`, and `set_nbhsP`.

- in file `lebesgue_measure.v`,
  + new lemmas `pointwise_almost_uniform`, and 
    `ae_pointwise_almost_uniform`.

- in `exp.v`:
  + lemmas `powRrM`, `gt0_ler_powR`,
    `gt0_powR`, `norm_powR`, `lt0_norm_powR`,
    `powRB`
  + lemmas `poweRrM`, `poweRAC`, `gt0_poweR`,
    `poweR_eqy`, `eqy_poweR`, `poweRD`, `poweRB`

- in `mathcomp_extra.v`:
  + definition `min_fun`, notation `\min`
  + new lemmas `maxr_absE`, `minr_absE`
- in `classical_sets.v`:
  + lemmas `set_predC`, `preimage_true`, `preimage_false`
- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_ltr`, `measurable_minr`
- in file `lebesgue_integral.v`,
  + new lemmas `lusin_simple`, and `measurable_almost_continuous`.
- in file `measure.v`,
  + new lemmas `finite_card_sum`, and `measureU2`.

- in `topology.v`:
  + lemma `bigsetU_compact`

- in `exp.v`:
  + notation `` e `^?(r +? s) ``
  + lemmas `expR_eq0`, `powRN`
  + definition `poweRD_def`
  + lemmas `poweRD_defE`, `poweRB_defE`, `add_neq0_poweRD_def`,
    `add_neq0_poweRB_def`, `nneg_neq0_poweRD_def`, `nneg_neq0_poweRB_def`
  + lemmas `powR_eq0`, `poweR_eq0`
- in file `lebesgue_integral.v`,
  + new lemma `approximation_sfun_integrable`.

- in `classical_sets.v`:
  + lemmas `properW`, `properxx`

- in `classical_sets.v`:
  + lemma `Zorn_bigcup`
  + lemmas `imsub1` and `imsub1P`

- in file `boolp.v`,
  + lemmas `notP`, `notE`
  + new lemma `implyE`.
  + new lemmas `contra_leP` and `contra_ltP`

- in file `reals.v`:
  + lemmas `sup_sumE`, `inf_sumE`
- in file `topology.v`:
  + lemma `ball_symE`
- in file `normedtype.v`,
  + new definition `edist`.
  + new lemmas `edist_ge0`, `edist_neqNy`, `edist_lt_ball`,
    `edist_fin`, `edist_pinftyP`, `edist_finP`, `edist_fin_open`, 
    `edist_fin_closed`, `edist_pinfty_open`, `edist_sym`, `edist_triangle`, 
    `edist_continuous`, `edist_closeP`, and `edist_refl`.
- in `constructive_ereal.v`:
  + lemmas `lte_pmulr`, `lte_pmull`, `lte_nmulr`, `lte_nmull`
  + lemmas `lte0n`, `lee0n`, `lte1n`, `lee1n`
  + lemmas `fine0` and `fine1`
- in `sequences.v`:
  + lemma `eseries_cond`
  + lemmas `eseries_mkcondl`, `eseries_mkcondr`

- in file `numfun.v`,
  + new lemma `continuous_bounded_extension`.
- in file `sequences.v`,
  + new lemmas `geometric_partial_tail`, and `geometric_le_lim`.
- in file `topology.v`,
  + new lemma `pointwise_cvgP`.

- in `classical_sets.v`:
  + lemma `bigcup_bigcup`

- in `topology.v`:
  + lemma `closed_bigcup`

- in `signed.v`:
  + lemmas `Posz_snum_subproof` and `Negz_snum_subproof`
  + canonical instances `Posz_snum` and `Negz_snum`

- in file `normedtype.v`,
  + new definitions `edist_inf`, `uniform_separator`, and `Urysohn`.
  + new lemmas `continuous_min`, `continuous_max`, `edist_closel`,
    `edist_inf_ge0`, `edist_inf_neqNy`, `edist_inf_triangle`,
    `edist_inf_continuous`, `edist_inf0`, `Urysohn_continuous`,
    `Urysohn_range`, `Urysohn_sub0`, `Urysohn_sub1`, `Urysohn_eq0`,
    `Urysohn_eq1`, `uniform_separatorW`, `normal_uniform_separator`,
    `uniform_separatorP`, `normal_urysohnP`, and
    `subset_closure_half`.

- in file `topology.v`,
  + new definition `normal_space`.
  + new lemmas `filter_inv`, and `countable_uniform_bounded`.

- in file `normedtype.v`,
  + new lemmas `normal_openP`, `normal_separatorP`, `uniform_regular`, 
    `regular_openP`, and `pseudometric_normal`.
- in file `topology.v`,
  + new definition `regular_space`.
  + new lemma `ent_closure`.


### Changed

- `mnormalize` moved from `kernel.v` to `measure.v` and generalized
- in `constructive_ereal.v`:
  + `lee_adde` renamed to `lee_addgt0Pr` and turned into a reflect
  + `lee_dadde` renamed to `lee_daddgt0Pr` and turned into a reflect

### Renamed

- in `boolp.v`:
  + `mextentionality` -> `mextensionality`
  + `extentionality` -> `extensionality`

- in `exp.v`:
  + `expK` -> `expRK`

- in `exp.v`:
  + `power_pos_eq0` -> `powR_eq0_eq0`
  + `power_pos_inv` -> `powR_invn`
  + `powere_pos_eq0` -> `poweR_eq0_eq0`

- in `exp.v`:
  + `power_pos` -> `powR`
  + `power_pos_ge0` -> `powR_ge0`
  + `power_pos_gt0` -> `powR_gt0`
  + `gt0_power_pos` -> `gt0_powR`
  + `power_pos0` -> `powR0`
  + `power_posr1` -> `powRr1`
  + `power_posr0` -> `powRr0`
  + `power_pos1` -> `powR1`
  + `ler_power_pos` -> `ler_powR`
  + `gt0_ler_power_pos` -> `gt0_ler_powR`
  + `power_posM` -> `powRM`
  + `power_posrM` -> `powRrM`
  + `power_posAC` -> `powRAC`
  + `power_posD` -> `powRD`
  + `power_posN` -> `powRN`
  + `power_posB` -> `powRB`
  + `power_pos_mulrn` -> `powR_mulrn`
  + `power_pos_inv1` -> `powR_inv1`
  + `power_pos_intmul` -> `powR_intmul`
  + `ln_power_pos` -> `ln_powR`
  + `power12_sqrt` -> `powR12_sqrt`
  + `norm_power_pos` -> `norm_powR`
  + `lt0_norm_power_pos` -> `lt0_norm_powR`

- in `lebesgue_measure.v`:
  + `measurable_power_pos` -> `measurable_powR`

- in `exp.v`:
  + `powere_pos` -> `poweR`
  + `powere_pos_EFin` -> `poweR_EFin`
  + `powere_posyr` -> `poweRyr`
  + `powere_pose0` -> `poweRe0`
  + `powere_pose1` -> `poweRe1`
  + `powere_posNyr` -> `poweRNyr`
  + `powere_pos0r` -> `poweR0r`
  + `powere_pos1r` -> `poweR1r`
  + `fine_powere_pos` -> `fine_poweR`
  + `powere_pos_ge0` -> `poweR_ge0`
  + `powere_pos_gt0` -> `poweR_gt0`
  + `powere_posM` -> `poweRM`
  + `powere12_sqrt` -> `poweR12_sqrt`

- in `lebesgue_integral.v`:
  + `ge0_integralM_EFin` -> `ge0_integralZl_EFin`
  + `ge0_integralM` -> `ge0_integralZl`
  + `integralM_indic` -> `integralZl_indic`
  + `integralM_indic_nnsfun` -> `integralZl_indic_nnsfun`
  + `integrablerM` -> `integrableZl`
  + `integrableMr` -> `integrableZr`
  + `integralM` -> `integralZl`

- in `classical_sets.v`:
  + `bigcup_set_cond` -> `bigcup_seq_cond`
  + `bigcup_set` -> `bigcup_seq`
  + `bigcap_set_cond` -> `bigcap_seq_cond`
  + `bigcap_set` -> `bigcap_seq`

- in `normedtype.v`:
  + `nbhs_closedballP` -> `nbhs_closed_ballP`
- in `normedtype.v`: 
  + `normal_urysohnP` -> `normal_separatorP`.

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
