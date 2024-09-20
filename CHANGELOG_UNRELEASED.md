# Changelog (unreleased)

## [Unreleased]

### Added

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

- in `mathcomp_extra.v`:
  + lemma `bij_forall`

- in `normedtype.v`:
  + lemma `cvgyNP`

- in `realfun.v`:
  + lemmas `cvg_pinftyP`, `cvg_ninftyP`

- in `topology.v`:
  + lemmas `in_nearW`, `open_in_nearW`
- in `classical_sets.v`:
  + lemma `not_setD1`

- in `measure.v`:
  + lemma `measurable_fun_set1`
- in file `classical_orders.v`,
  + new definitions `share_prefix`, `first_diff`, `lexi_bigprod`, `start_with`,
    `big_lexi_order`, and `big_lexi_ord`.
  + new lemmas `share_prefix0`, `share_prefixC`, `share_prefixS`,
    `share_prefix_refl`, `share_prefix_trans`, `first_diffC`,
    `first_diff_unique`, `first_diff_SomeP`, `first_diff_NoneP`,
    `first_diff_lt`, `first_diff_eq`, `first_diff_dfwith`,
    `lexi_bigprod_reflexive`, `lexi_bigprod_anti`, `lexi_bigprod_trans`,
    `lexi_bigprod_total`, `start_with_prefix`, `lexi_bigprod_prefix_lt`,
    `lexi_bigprod_prefix_gt`, `lexi_bigprod_between`,
    `big_lexi_interval_prefix`, and `shared_prefix_closed_itv`.

### Changed

- in `numfun.v`:
  + lemma `gt0_funeposM` renamed to `ge0_funeposM`
    and hypothesis weakened from strict to large inequality
  + lemma `gt0_funenegM` renamed to `ge0_funenegM`
    and hypothesis weakened from strict to large inequality
  + lemma `lt0_funeposM` renamed to `le0_funeposM`
    and hypothesis weakened from strict to large inequality
  + lemma `lt0_funenegM` renamed to `le0_funenegM`
    and hypothesis weakened from strict to large inequality

### Renamed

### Generalized

- in `constructive_ereal.v`:
  + lemmas `maxeMr`, `maxeMl`, `mineMr`, `mineMr`:
    hypothesis weakened from strict inequality to large inequality
- in `lebesgue_integral.v`:
  + lemma `integral_setD1_EFin`
  + lemmas `integral_itv_bndo_bndc`, `integral_itv_obnd_cbnd`
  + lemmas `Rintegral_itv_bndo_bndc`, `Rintegral_itv_obnd_cbnd`

### Deprecated

### Removed

### Infrastructure

### Misc
