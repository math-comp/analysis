# Changelog (unreleased)

## [Unreleased]

### Added

- file `mathcomp_extra.v`
  + lemmas `ge_trunc`, `lt_succ_trunc`, `trunc_ge_nat`, `trunc_lt_nat`

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)
  + lemmas `RabsE`, `RdistE`, `sum_f_R0E`, `factE`

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- file `constructive_ereal.v`:
  + definition `iter_mule`
  + lemma `prodEFin`

- file `exp.v`:
  + lemma `expR_sum`

- file `lebesgue_integral.v`:
  + lemma `measurable_fun_le`

- in `trigo.v`:
  + lemma `integral0oo_atan`

- in `measure.v`:
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`
  + lemma `preimage_set_system_id`

- in `Rstruct_topology.v`:
  + lemma `RexpE`

- in `boolp.v`:
  + lemmas `orW`, `or3W`, `or4W`

- in `classical_sets.v`:
  + lemma `image_nonempty`

- in `mathcomp_extra.v`:
  + lemmas `eq_exists2l`, `eq_exists2r`

- in `ereal.v`:
  + lemmas `ereal_infEN`, `ereal_supN`, `ereal_infN`, `ereal_supEN`
  + lemmas `ereal_supP`, `ereal_infP`, `ereal_sup_gtP`, `ereal_inf_ltP`,
    `ereal_inf_leP`, `ereal_sup_geP`, `lb_ereal_infNy_adherent`,
    `ereal_sup_real`, `ereal_inf_real`

- in `charge.v`:
  + lemma `ae_eq_mul2l`

- in `hoelder.v`
  + lemmas `Lnorm0`, `oppr_Lnorm`, `Lnorm_cst1`
  + definition `conjugate`
  + lemma `conjugateE`
  + lemmas `lerB_DLnorm`, `lerB_LnormD`, `eminkowski`

- in `lebesgue_integral.v`:
  + lemma `mfunMn`

- in `classical_sets.v`:
  + lemma `set_cst`

- in `measurable_realfun.v`:
  + lemmas `ereal_inf_seq`, `ereal_sup_seq`,
    `ereal_sup_cst`, `ereal_inf_cst`, `ereal_sup_pZl`,
    `ereal_supZl`, `ereal_inf_pZl`, `ereal_infZl`

- in `measure.v`:
  + lemmas `seqDU_measurable`, `measure_gt0`
  + notation `\forall x \ae mu , P`
  + notations `f = g %[ae mu in D ]`, `f = g %[ae mu ]`
  + module `ProperNotations` with notations `++>`, `==>`, `~~>`
  + instances `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
  + lemmas `ae_eq_comp2`, `ae_foralln`

- in `functions.v`:
  + lemma `natmulfctE`

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

- new file `lspace.v`:
  + definition `finite_norm`
  + mixin `isLfun` with field `lfuny`
  + structure `Lfun`
  + notation `LfunType`
  + definition `Lequiv`
  + canonical `Lequiv_canonical`
  + definition `LspaceType`
  + canonicals `LspaceType_quotType`, `LspaceType_eqType`, `LspaceType_choiceType`,
    `LspaceType_eqQuotType`
  + lemma `LequivP`
  + record `LType`
  + coercion `LfunType_of_LType`
  + definition `Lspace` with notation `mu.-Lspace p`
  + lemma `LType1_integrable`, `LType2_integrable_sqr`
  + definitions `finlfun`, `lfun`, `lfun_key`
  + canonical `lfun_keyed`
  + lemmas `sub_lfun_mfun`, `sub_lfun_finlfun`
  + definition `lfun_Sub`
  + lemmas `lfun_rect`, `lfun_valP`, `lfuneqP`, `lfuny0`, `mfunP`, `lfunP`,
    `mfun_scaler_closed`
  + lemmas `LnormZ`, `lfun_submod_closed`
  + lemmas `finite_norm_fine`, `ler_LnormD`,
    `LnormN`, `Lnorm_natmul`, `fine_Lnorm_eq0`
  + lemma `Lspace_inclusion`

- in `nat_topology.v`:
  + lemma `nbhs_infty_gtr`

### Changed

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package
- moved from `gauss_integral` to `trigo.v`:
  + `oneDsqr`, `oneDsqr_ge1`, `oneDsqr_inum`, `oneDsqrV_le1`,
    `continuous_oneDsqr`, `continuous_oneDsqr`
- moved, generalized, and renamed from `gauss_integral` to `trigo.v`:
  + `integral01_oneDsqr` -> `integral0_oneDsqr`

- in `hoelder.v`:
  + lemmas `Lnorm_eq0_eq0`

- in `lebesgue_integral.v`:
  + lemmas `ae_eq_integral_abs`, `ge0_ae_eq_integral`, `ae_eq_integral`

- in `measurable.v`
  + from instance to definitions: `ae_filter_ringOfSetsType`, `ae_properfilter_algebraOfSetsType`
  + definiton `ae_eq`
  + definition `ess_sup` moved to `ess_sup_inf.v`

### Renamed

- in `lebesgue_integral.v`:
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`
  + `measurable_funP` -> `measurable_funPT` (field of `isMeasurableFun` mixin)

- in `mathcomp_extra.v`
  + `comparable_min_le_min` -> `comparable_le_min2`
  + `comparable_max_le_max` -> `comparable_le_max2`
  + `min_le_min` -> `le_min2`
  + `max_le_max` -> `le_max2`
  + `real_sqrtC` -> `sqrtC_real`

- in `ereal.v`:
  + `ereal_sup_le` -> `ereal_sup_ge`

- in `hoelder.v`:
  + `minkowski` -> `minkowski_EFin`

### Generalized

- in `constructive_ereal.v`:
  + lemma `EFin_natmul`

- in `lebesgue_integral.v`
  + lemmas `measurable_funP`, `ge0_integral_pushforward`,
    `integrable_pushforward`, `integral_pushforward`

- in `hoelder.v`:
  + definition `Lnorm` generalized to functions with codomain `\bar R`
    (this impacts the notation `'N_p[f]`)

### Deprecated

### Removed

- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)
  + lemma `deg_le2_ge0` (available as `deg_le2_poly_ge0` in `ssrnum.v`
    since MathComp 2.1.0)

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`

### Infrastructure

### Misc
