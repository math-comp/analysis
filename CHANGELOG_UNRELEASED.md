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
  + new definition `set_nbhs`.
  + new lemmas `filterI_iter_sub`, `filterI_iterE`, `finI_fromI`, 
    `filterI_iter_finI`, `smallest_filter_finI`, and `set_nbhsP`.

- in file `lebesgue_measure.v`,
  + new lemmas `pointwise_almost_uniform`, and 
    `ae_pointwise_almost_uniform`.

- in `exp.v`:
  + lemmas `power_posrM`, `gt0_ler_power_pos`,
    `gt0_power_pos`, `norm_power_pos`, `lt0_norm_power_pos`,
    `power_posB`
  + lemmas `powere_posrM`, `powere_posAC`, `gt0_powere_pos`,
    `powere_pos_eqy`, `eqy_powere_pos`, `powere_posD`, `powere_posB`

- in `mathcomp_extra.v`:
  + definition `min_fun`, notation `\min`
- in `classical_sets.v`:
  + lemmas `set_predC`, `preimage_true`, `preimage_false`
- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_ltr`, `measurable_minr`

### Changed

- moved from `lebesgue_measure.v` to `real_interval.v`:
  + lemmas `set1_bigcap_oc`, `itv_bnd_open_bigcup`, `itv_open_bnd_bigcup`,
    `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`
  
- moved from `functions.v` to `classical_sets.v`: `subsetP`.

### Renamed

- in `boolp.v`:
  + `mextentionality` -> `mextensionality`
  + `extentionality` -> `extensionality`
- in `exp.v`:
  + `expK` -> `expRK`

### Generalized

- in `exp.v`:
  + lemmas `convex_expR`, `ler_power_pos`
- in `exp.v`:
  + lemma `ln_power_pos`

### Deprecated

### Removed

### Infrastructure

### Misc
