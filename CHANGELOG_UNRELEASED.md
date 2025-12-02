# Changelog (unreleased)

## [Unreleased]

### Added

- in `classical_sets.v`:
  + lemma `nonemptyPn`

- in `cardinality.v`:
  + lemma `infinite_setD`

- in `convex.v`:
  + lemmas `convN`, `conv_le`

- in `normed_module.v`:
  + lemma `limit_point_infinite_setP`
- in `measure_negligible.v`:
  + definition `null_set` with notation `_.-null_set`
  + lemma `subset_null_set`
  + lemma `negligible_null_set`
  + lemma `measure0_null_setP`
  + lemma `null_setU`
  + definition `null_dominates`
  + lemma `null_dominates_trans`
  + lemma `null_content_dominatesP`

- in `charge.v`:
  + definition `charge_dominates`
  + lemma `charge_null_dominatesP`
  + lemma `content_charge_dominatesP`

- in `sequences.v`:
  + lemma `increasing_seq_injective`
  + definition `adjacent_set`
  + lemmas `adjacent_sup_inf`, `adjacent_sup_inf_unique`
  + definition `cut`
  + lemmas `cut_adjacent`, `infinite_bounded_limit_point_nonempty`

### Changed

- in `charge.v`:
  + `dominates_cscalel` specialized from
    `set _ -> \bar _` to `{measure set _ -> \bar _}`

- in `measurable_structure.v`:
  + the notation ``` `<< ``` is now for `null_set_dominates`,
    the previous definition can be recovered with the lemma
    `null_dominatesP`

### Renamed

- in `probability.v`:
  + `derivable_oo_continuous_bnd_onemXnMr` -> `derivable_oo_LRcontinuous_onemXnMr`
- in `measure_negligible.v`:
  + `measure_dominates_ae_eq` -> `null_dominates_ae_eq`

- in `charge.v`:
  + `induced` -> `induced_charge`

### Generalized

- in `lebesgue_integral_under.v`:
  + weaken an hypothesis of lemma `continuity_under_integral`

- in `lebesgue_integrable.v`:
  + weaken an hypothesis of lemma `finite_measure_integrable_cst`

### Deprecated

### Removed

- in `lebesgue_stieltjes_measure.v`:
  + notation `wlength_sigma_sub_additive` (deprecated since 1.1.0)

- in `constructive_ereal.v`:
  + notations `gee_pmull`, `gee_addl`, `gee_addr`, `gte_addr`, `gte_addl`,
    `lte_subl_addr`, `lte_subl_addl`, `lte_subr_addr`, `lte_subr_addl`,
    `lee_subl_addr`, `lee_subl_addl`, `lee_subr_addr`, `lee_subr_addl`
    (deprecated since 1.2.0)

- in `signed.v`:
  + notations `num_le_maxr`, `num_le_maxl`, `num_le_minr`, `num_le_minl`,
    `num_lt_maxr`, `num_lt_maxl`, `num_lt_minr`, `num_lt_minl`
    (deprecated since 1.2.0)

- in `measure_function.v`:
  + notations `g_salgebra_measure_unique_trace`,
    `g_salgebra_measure_unique_cover`, `g_salgebra_measure_unique`
    (deprecated since 1.2.0)

- in `measurable_structure.v`:
  + notations `monotone_class`, `monotone_class_g_salgebra`,
    `smallest_monotone_classE`, `monotone_class_subset`,
    `setI_closed_gdynkin_salgebra`, `dynkin_g_dynkin`, `dynkin_monotone`,
    `salgebraType`
    (deprecated since 1.2.0)

- in `sequences.v`:
  + notation `eq_bigsetU_seqD`
    (deprecated since 1.2.0)
- in `measurable_structure.v`:
  + definition `measure_dominates` (use `null_set_dominates` instead)
  + lemma `measure_dominates_trans`

- in `charge.v`:
  + lemma `dominates_charge_variation` (use `charge_null_dominatesP` instead)

### Infrastructure

### Misc
