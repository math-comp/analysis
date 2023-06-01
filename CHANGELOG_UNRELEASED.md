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
  + lemmas `powRrM`, `gt0_ler_powR`,
    `gt0_powR`, `norm_powR`, `lt0_norm_powR`,
    `powRB`
  + lemmas `poweRrM`, `poweRAC`, `gt0_poweR`,
    `poweR_eqy`, `eqy_poweR`, `poweRD`, `poweRB`

- in `mathcomp_extra.v`:
  + definition `min_fun`, notation `\min`
- in `classical_sets.v`:
  + lemmas `set_predC`, `preimage_true`, `preimage_false`
- in `lebesgue_measure.v`:
  + lemmas `measurable_fun_ltr`, `measurable_minr`

- in `exp.v`:
  + notation `` e `^?(r +? s) ``
  + lemmas `expR_eq0`, `powRN`
  + definition `poweRD_def`
  + lemmas `poweRD_defE`, `poweRB_defE`, `add_neq0_poweRD_def`,
    `add_neq0_poweRB_def`, `nneg_neq0_poweRD_def`, `nneg_neq0_poweRB_def`
  + lemmas `powR_eq0`, `poweR_eq0`

### Changed

- moved from `lebesgue_measure.v` to `real_interval.v`:
  + lemmas `set1_bigcap_oc`, `itv_bnd_open_bigcup`, `itv_open_bnd_bigcup`,
    `itv_bnd_infty_bigcup`, `itv_infty_bnd_bigcup`
  
- moved from `functions.v` to `classical_sets.v`: `subsetP`.

- in `exp.v`:
  + lemmas `power_posD` (now `powRD`), `power_posB` (now `powRB`)

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

### Generalized

- in `exp.v`:
  + lemmas `convex_expR`, `ler_power_pos` (now `ler_powR`)
- in `exp.v`:
  + lemma `ln_power_pos` (now `ln_powR`)

### Deprecated

### Removed

### Infrastructure

### Misc
