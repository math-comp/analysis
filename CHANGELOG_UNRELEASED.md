# Changelog (unreleased)

## [Unreleased]

### Added

- in `num_topology.v`:
  + lemma `in_continuous_mksetP`

- in `normedtype.v`:
  + lemmas `continuous_within_itvcyP`, `continuous_within_itvNycP`

- in `mathcomp_extra.v`:
  + lemma `partition_disjoint_bigfcup`
- in `lebesgue_measure.v`:
  + lemma `measurable_indicP`

- in `lebesgue_integral.v`:
  + definition `dyadic_approx` (was `Let A`)
  + definition `integer_approx` (was `Let B`)
  + lemma `measurable_sum`
  + lemma `integrable_indic`

- in `constructive_ereal.v`:
  + notations `\prod` in scope ereal_scope
  + lemmas `prode_ge0`, `prode_fin_num`
- in `probability.v`:
  + lemma `expectation_def`
  + notation `'M_`

### Changed

- in `lebesgue_integrale.v`
  + change implicits of `measurable_funP`
  
### Renamed

- in `lebesgue_measure.v`:
  + `measurable_fun_indic` -> `measurable_indic`
  + `emeasurable_fun_sum` -> `emeasurable_sum`
  + `emeasurable_fun_fsum` -> `emeasurable_fsum`
  + `ge0_emeasurable_fun_sum` -> `ge0_emeasurable_sum`
- in `probability.v`:
  + `expectationM` -> `expectationMl`

- in `classical_sets.v`:
  + `preimage_itv_o_infty` -> `preimage_itvoy`
  + `preimage_itv_c_infty` -> `preimage_itvcy`
  + `preimage_itv_infty_o` -> `preimage_itvNyo`
  + `preimage_itv_infty_c` -> `preimage_itvNyc`

- in `constructive_ereal.v`:
  + `maxeMr` -> `maxe_pMr`
  + `maxeMl` -> `maxe_pMl`
  + `mineMr` -> `mine_pMr`
  + `mineMl` -> `mine_pMl`

### Generalized

- in `probability.v`:
  + definition `random_variable`
  + lemmas `notin_range_measure`, `probability_range`
  + definition `distribution`
  + lemma `probability_distribution`, `integral_distribution`
  + mixin `MeasurableFun_isDiscrete`
  + structure `discreteMeasurableFun`
  + definition `discrete_random_variable`
  + lemma `dRV_dom_enum`
  + definitions `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV`, `sum_enum_prob`

### Deprecated

- in file `lebesgue_integral.v`:
  + lemma `approximation`

### Removed

- in `lebesgue_integral.v`:
  + lemma `measurable_indic` (was uselessly specializing `measurable_fun_indic` (now `measurable_indic`) from `lebesgue_measure.v`)
  + notation `measurable_fun_indic` (deprecation since 0.6.3)
- in `constructive_ereal.v`
  + notation `lee_opp` (deprecated since 0.6.5)
  + notation `lte_opp` (deprecated since 0.6.5)
- in `measure.v`:
  + `dynkin_setI_bigsetI` (use `big_ind` instead)

### Infrastructure

### Misc
