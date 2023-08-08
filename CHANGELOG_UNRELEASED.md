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
- in file `lebesgue_integral.v`,
  + new lemmas `integral_le_bound`, `continuous_compact_integrable`, and 
    `lebesgue_differentiation_continuous`.

- in `normedtype.v`:
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`

### Changed

- `mnormalize` moved from `kernel.v` to `measure.v` and generalized
- in `constructive_ereal.v`:
  + `lee_adde` renamed to `lee_addgt0Pr` and turned into a reflect
  + `lee_dadde` renamed to `lee_daddgt0Pr` and turned into a reflect

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
