# Changelog (unreleased)

## [Unreleased]

### Added

- in file `cantor.v`,
  + new definitions `cantor_space`, `cantor_like`, `pointed_discrete`, and 
    `tree_of`.
  + new lemmas `cantor_space_compact`, `cantor_space_hausdorff`, 
    `cantor_zero_dimensional`, `cantor_perfect`, `cantor_like_cantor_space`, 
    `tree_map_props`, `homeomorphism_cantor_like`, and 
    `cantor_like_finite_prod`.
  + new theorem `cantor_surj`.
- in file `topology.v`,
  + new lemmas `perfect_set2`, and `ent_closure`.
  + lemma `clopen_surj`

- in `normedtype.v`:
  + hints for `at_right_proper_filter` and `at_left_proper_filter`

- in `realfun.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`,
    `increasing_fun`, `decreasing_fun`
  + lemmas `cvg_addrl`, `cvg_addrr`, `cvg_centerr`, `cvg_shiftr`,
    `nondecreasing_cvgr`,
	`nonincreasing_at_right_cvgr`,
	`nondecreasing_at_right_cvgr`,
	`nondecreasing_cvge`, `nondecreasing_is_cvge`,
	`nondecreasing_at_right_cvge`, `nondecreasing_at_right_is_cvge`,
	`nonincreasing_at_right_cvge`, `nonincreasing_at_right_is_cvge`
- in `ereal.v`:
  + lemmas `ereal_sup_le`, `ereal_inf_le`

- in `normedtype.v`:
  + definition `lower_semicontinuous`
  + lemma `lower_semicontinuousP`

- in `numfun.v`:
  + lemma `patch_indic`

- in `lebesgue_measure.v`
  + lemma `lower_semicontinuous_measurable`

- in `lebesgue_integral.v`:
  + definition `locally_integrable`
  + lemmas `integrable_locally`, `locally_integrableN`, `locally_integrableD`,
    `locally_integrableB`
  + definition `iavg`
  + lemmas `iavg0`, `iavg_ge0`, `iavg_restrict`, `iavgD`
  + definitions `HL_maximal`
  + lemmas `HL_maximal_ge0`, `HL_maximalT_ge0`,
    `lower_semicontinuous_HL_maximal`, `measurable_HL_maximal`,
    `maximal_inequality`

- in file `measure.v`
  + add lemmas `ae_eq_subset`, `measure_dominates_ae_eq`.

- in `charge.v`
  + definition `charge_of_finite_measure` (instance of `charge`)
  + lemmas `dominates_cscalel`, `dominates_cscaler`
  + definition `cpushforward` (instance of `charge`)
  + lemma `dominates_pushforward`
  + lemma `cjordan_posE`
  + lemma `jordan_posE`
  + lemma `cjordan_negE`
  + lemma `jordan_negE`
  + lemma `Radon_Nikodym_sigma_finite`
  + lemma `Radon_Nikodym_fin_num`
  + lemma `Radon_Nikodym_integral`
  + lemma `ae_eq_Radon_Nikodym_SigmaFinite`
  + lemma `Radon_Nikodym_change_of_variables`
  + lemma `Radon_Nikodym_cscale`
  + lemma `Radon_Nikodym_cadd`
  + lemma `Radon_Nikodym_chain_rule`

- in `sequences.v`:
  + lemma `minr_cvg_0_cvg_0`
  + lemma `mine_cvg_0_cvg_fin_num`
  + lemma `mine_cvg_minr_cvg`
  + lemma `mine_cvg_0_cvg_0`
  + lemma `maxr_cvg_0_cvg_0`
  + lemma `maxe_cvg_0_cvg_fin_num`
  + lemma `maxe_cvg_maxr_cvg`
  + lemma `maxe_cvg_0_cvg_0`
- in `constructive_ereal.v`
  + lemma `lee_subgt0Pr`

- in `topology.v`:
  + lemma `nbhs_dnbhs_neq`

- in `normedtype.v`:
  + lemma `not_near_at_rightP`

- in `realfun.v`:
  + lemma `cvg_at_right_left_dnbhs`
  + lemma `cvg_at_rightP`
  + lemma `cvg_at_leftP`
  + lemma `cvge_at_rightP`
  + lemma `lime_sup`
  + lemma `lime_inf`
  + lemma `lime_supE`
  + lemma `lime_infE`
  + lemma `lime_infN`
  + lemma `lime_supN`
  + lemma `lime_sup_ge0`
  + lemma `lime_inf_ge0`
  + lemma `lime_supD`
  + lemma `lime_sup_le`
  + lemma `lime_inf_sup`
  + lemma `lim_lime_inf`
  + lemma `lim_lime_sup`

- in `normedtype.v`:
  + lemmas `withinN`, `at_rightN`, `at_leftN`, `cvg_at_leftNP`, `cvg_at_rightNP`

- in `topology.v`:
  + lemma `dnbhs_ball`

- in `normedtype.v`
  + definitions `limf_esup`, `limf_einf`
  + lemmas `limf_esupE`, `limf_einfE`, `limf_esupN`, `limf_einfN`

- in `sequences.v`:
  + lemmas `limn_esup_lim`, `limn_einf_lim`

- in `realfun.v`:
  + lemmas `lime_sup_lim`, `lime_inf_lim`

### Changed

- in `normedtype.v`:
  + lemmas `vitali_lemma_finite` and `vitali_lemma_finite_cover` now returns
    duplicate-free lists of indices

- moved from `lebesgue_integral.v` to `measure.v`:
  + definition `ae_eq`
  + lemmas
	`ae_eq0`,
	`ae_eq_comp`,
	`ae_eq_funeposneg`,
	`ae_eq_refl`,
	`ae_eq_trans`,
	`ae_eq_sub`,
	`ae_eq_mul2r`,
	`ae_eq_mul2l`,
	`ae_eq_mul1l`,
	`ae_eq_abse`

- in `charge.v`
  + definition `jordan_decomp` now uses `cadd` and `cscale`
  + definition `Radon_Nikodym_SigmaFinite` now in a module `Radon_Nikodym_SigmaFinite` with
    * definition `f`
    * lemmas `f_ge0`, `f_fin_num`, `f_integrable`, `f_integral`
    * lemma `change_of_variables`
    * lemma `integralM`
    * lemma `chain_rule`

- in `sequences.v`:
  + change the implicit arguments of `trivIset_seqDU`
- moved from `topology.v` to `mathcomp_extra.v`
  + definition `monotonous`

- in `sequences.v`:
  + `limn_esup` now defined from `lime_sup`
  + `limn_einf` now defined from `limn_esup`
  
### Renamed

- in `exp.v`:
  + `lnX` -> `lnXn`
- in `charge.v`:
  + `dominates_caddl` -> `dominates_cadd`

### Generalized

- in `lebesgue_integral.v`
  + `ge0_integral_bigsetU` generalized from `nat` to `eqType`
- in `lebesgue_measure.v`
  + an hypothesis of lemma `integral_ae_eq` is weakened

### Deprecated

### Removed

- in `forms.v`:
  + lemmas `eq_map_mx`, `map_mx_id`

### Infrastructure

### Misc
