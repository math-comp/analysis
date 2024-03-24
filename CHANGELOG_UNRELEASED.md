# Changelog (unreleased)

## [Unreleased]

### Added

- in `exp.v`
  + lemma `ln_lt0`

- in `lebesgue_integral.v`
  + lemma `ge0_integralZr`

- in `contra.v`:
  + in module `Internals`
    * variant `equivT`
    * definitions `equivT_refl`, `equivT_transl`, `equivT_sym`, `equivT_trans`,
      `equivT_transr`, `equivT_Prop`, `equivT_LR` (hint view), `equivT_RL` (hint view)
  + definition `notP`
  + hint view for `move/` and `apply/` for `Internals.equivT_LR`, `Internals.equivT_RL`

### Changed

- move from `kernel.v` to `measure.v`
  + definition `mset`, `pset`, `pprobability`
  + lemmas `lt0_mset`, `gt1_mset`

- in `measure.v`:
  + lemma `sigma_finiteP` generalized to an equivalence and changed to use `[/\ ..., .. & ....]`

### Renamed

- in `constructive_ereal.v`:
  + `lee_addl` -> `leeDl`
  + `lee_addr` -> `leeDr`
  + `lee_add2l` -> `leeD2l`
  + `lee_add2r` -> `leeD2r`
  + `lee_add` -> `leeD`
  + `lee_sub` -> `leeB`
  + `lee_add2lE` -> `leeD2lE`
  + `lte_add2lE` -> `lteD2lE`
  + `lee_oppl` -> `leeNl`
  + `lee_oppr` -> `leeNr`
  + `lte_oppr` -> `lteNr`
  + `lte_oppl` -> `lteNl`
  + `lte_add` -> `lteD`
  + `lte_addl` -> `lteDl`
  + `lte_addr` -> `lteDr`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
