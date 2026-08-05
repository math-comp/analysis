# Changelog (unreleased)

## [Unreleased]

### Added

- in `pseudometric_normed_Zmodule.v`:
  + lemmas `cvg0D`, `cvgD0`, `cvg0B`, `cvgB0`, `cvgN0`

- in `normed_module.v`:
  + lemmas `cvg1M`, `cvgM1`, `cvg0M`, `cvgM0`
  + lemmas `cvg1Z`, `cvg0Z`, `cvgZ0`

- in `function_spaces.v`:
  + lemma `within_continuous_big`

- in `nat_topology.v`:
  + lemma `near_infty_leq`

- in `num_topology.v`:
  + lemmas `at_rightD`, `at_leftD`, `near_at_rightD`, `near_at_leftD`,
    `at_left_shift`, `at_right_shift`

### Changed

- in `derive.v`:
  + instance `is_derive_mx` is now a lemma
- in `realsum.v`:
  + lemma `__admitted__psumB` proved and renamed to `psumB`

- moved from `measurable_structure.v` to `classical_sets.v`:
  + definition `preimage_set_system`
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
    `preimage_set_system_id`
  
- moved from `measurable_structure.v` to `classical_sets.v`:
  + definition `preimage_set_system`
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`,
    `preimage_set_system_id`

- moved from `topology_structure.v` to `filter.v`:
  + lemma `continuous_comp` (and generalized)

- in `numfun.v`:
  + `fune_abse` renamed to `funeposDneg` and direction of the equality changed
  + `funeposneg` renamed to `funeposBneg` and direction of the equality changed
  + `funeD_posD` renamed to `funeDB` and direction of the equality changed

- in `constructive_ereal.v`:
  + lemmas `EFin_semi_additive` and `dEFin_semi_additive` turned into `Let`s

- moved from `charge.v` to `signed_measure.v`:
  + mixin `isAdditiveCharge`, structure `AdditiveCharge`
  + mixin `isSemiSigmaAdditive`, structure `Charge`
  + factory `isCharge`
  + lemmas `charge0`, `charge_semi_additiveW`, `charge_semi_additive2E`,
    `charge_semi_additive2`, `chargeU`, `chargeDI`, `charge_partition`
  + definitions `measure_of_charge`, `charge_of_finite_measure`
  + lemma `chargeD`
  + definitions `crestr`, `crestr0`, `czero`, `cscale`
  + lemmas `dominates_cscalel`, `dominates_cscaler`
  + definition `copp`
  + lemma `cscaleN1`
  + definition `cadd`
  + lemmas `dominates_cadd`, `dominates_pushforward`
  + definitions `positive_set`, `negative_set`
  + lemmas `negative_set_charge_le0`, `negative_set0`,
    `positive_negative0`, `bigcup_negative_set`, `negative_setU`,
    `hahn_decomposition_lemma`
  + definition `hahn_decomposition`
  + theorem `Hahn_decomposition`
  + lemmas `Hahn_decomposition_uniq`, `cjordan_posE`, `cjordan_negE`
  + definitions `jordan_pos`, `jordan_neg`
  + lemmas `jordan_posE`, `jordan_negE`, `jordan_decomp`, `jordan_pos_dominates`,
    `jordan_neg_dominates`
  + definition `charge_variation`, `charge_dominates`
  + lemmas `abse_charge_variation`, `null_charge_dominatesP`,
    `content_charge_dominatesP`, `charge_variation_continuous`

- moved from `charge.v` to `radon_nikodym.v`:
  + definition `induced_charge`
  + lemmas `semi_sigma_additive_nng_induced`, `dominates_induced`,
    `integral_normr_continuous`
  + definitions `approxRN`, `int_approxRN`, `sup_int_approxRN`
  + lemmas `sup_int_approxRN_ge0`, `radon_nikodym_finite`,
    `radon_nikodym_sigma_finite`, `change_of_variables`, `integrableM`,
    `chain_rule`
  + definition `Radon_Nikodym`
  + lemmas `Radon_NikodymE`, `Radon_Nikodym_fin_num`, `Radon_Nikodym_integrable`,
    `ae_eq_Radon_Nikodym_SigmaFinite`, `Radon_Nikodym_change_of_variables`,
    `Radon_Nikodym_cscale`, `Radon_Nikodym_cadd`, `Radon_Nikodym_chain_rule`
- in `realsum.v`:
  + the following now use `funrpos` and `funrneg`:
    * definition `sum`
    * lemmas `summable_funrpos`, `summable_funrneg`
  + lemma `sum0` (now uses `cst`)

- moved from `realsum` to `numfun.v`:
  + now use `funrpos` and `funrneg`:
    * lemmas `eq_funrpos`, `eq_funrneg`
    * lemma `fpos0` (renamed to `funrpos_cst0`)
    * lemma `fneg0` (renamed to `funrneg_cst0`)
    * lemmas `funrposZ`, `funrnegZ`
    * lemmas `funrpos_natrM`, `funrneg_natrM`
    * lemmas `le_funrpos_norm`

- moved from `numfun.v` to `unstable.v`:
  + notations `nondecreasing_fun`, `nonincreasing_fun`,
    `decreasing_fun`, `increasing_fun`

- in `esum.v`:
  + definition `esum`
  + lemma `esum_fset`
  + lemma `esum_ge` -> `PosEsum.pos_esum_ge`
  + lemma `le_esum` -> `PosEsum.le_pos_esum`

- moved from `normed_module.v` to `metric_structure.v`
  + lemma `squeeze_cvgr`

- moved from `pseudometric_normed_Zmodule.v` to `metric_structure.v`
  + lemmas `real_cvgr_lt`, `real_cvgr_le`, `real_cvgr_le`, `real_cvgr_gt`
  + lemmas `cvgr_lt`, `cvgr_gt`, `cvgr_ge`, `cvgr_le`
- in `normal_distribution.v:
  + `normal_fun_center` -> `normal_fun_center0`

- moved from `measurable_structure.v` to `measure_function.v`:
  + definition `subset_sigma_subadditive`

- moved from `measurable_structure.v` to `unstable.v`:
  + notations `nondecreasing_seq`, `nonincreasing_seq`

- moved from `measurable_structure.v` to `classical_sets.v`:
  + notation `^nat`
  + defintion `sequence`
  + defintion `seqDU`
  + lemmas `seqDU_bigcup_eq`, `trivIset_seqDU`
  + definition `seqD`
  + lemmas `eq_bigcup_seqD`, `trivIset_seqD`, `seqDU_seqD`, `bigcup_bigsetU_bigcup`

- in `functions.v`
  + lemma `fctE` (include `zerofctE` and `onefctE`)

- in `classical_sets.v`
  + lemma `bigcupDr` -> `setD_bigcupr` (deprecating `bigcupDr`)

- moved from `metric_structure.v` to `num_topology.v`: 
  + lemma `cvg_at_right_left_dnbhs`, generalized to `topologicalType` from `metricType`.

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
