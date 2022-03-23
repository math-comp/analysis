# Changelog (unreleased)

## [Unreleased]

### Added

- in `signed.v`:
  + notations `%:nngnum` and `%:posnum`
- in `ereal.v`:
  + notations `{posnum \bar R}` and `{nonneg \bar R}`
  + notations `%:pos` and `%:nng` in `ereal_dual_scope` and `ereal_scope`
  + variants `posnume_spec` and `nonnege_spec`
  + definitions `posnume`, `nonnege`, `abse_reality_subdef`,
    `ereal_sup_reality_subdef`, `ereal_inf_reality_subdef`
  + lemmas `ereal_comparable`, `pinfty_snum_subproof`, `ninfty_snum_subproof`,
    `EFin_snum_subproof`, `fine_snum_subproof`, `oppe_snum_subproof`,
    `adde_snum_subproof`, `dadde_snum_subproof`, `mule_snum_subproof`,
    `abse_reality_subdef`, `abse_snum_subproof`, `ereal_sup_snum_subproof`,
    `ereal_inf_snum_subproof`, `num_abse_eq0`, `num_lee_maxr`, `num_lee_maxl`,
    `num_lee_minr`, `num_lee_minl`, `num_lte_maxr`, `num_lte_maxl`,
    `num_lte_minr`, `num_lte_minl`, `num_abs_le`, `num_abs_lt`,
    `posnumeP`, `nonnegeP`
  + signed instances `pinfty_snum`, `ninfty_snum`, `EFin_snum`, `fine_snum`,
    `oppe_snum`, `adde_snum`, `dadde_snum`, `mule_snum`, `abse_snum`,
    `ereal_sup_snum`, `ereal_inf_snum`

### Changed

- in `functions.v`:
  + `addrfunE` renamed to `addrfctE` and generalized to `Type`, `zmodType`
  + `opprfunE` renamed to `opprfctE` and generalized to `Type`, `zmodType`
- moved from `functions.v` to `classical_sets.v`
  + lemma `subsetW`, definition `subsetCW`
- in `mathcomp_extra.v`:
  + fix notation `ltLHS`

### Renamed

- in `topology.v`:
  + `open_bigU` -> `bigcup_open`
- in `functions.v`:
  + `mulrfunE` -> `mulrfctE`
  + `scalrfunE` -> `scalrfctE`
  + `exprfunE` -> `exprfctE`
  + `valLr` -> `valR`
  + `valLr_fun` -> `valR_fun`
  + `valLrK` -> `valRK`
  + `oinv_valLr` -> `oinv_valR`
  + `valLr_inj_subproof` -> `valR_inj_subproof`
  + `valLr_surj_subproof` -> `valR_surj_subproof`
- in `measure.v`:
  + `measurable_bigcup` -> `bigcupT_measurable`
  + `measurable_bigcap` -> `bigcapT_measurable`
  + `measurable_bigcup_rat` -> `bigcupT_measurable_rat`
- in `lebesgue_measure.v`:
  + `emeasurable_bigcup` -> `bigcupT_emeasurable`

### Removed

- files `posnum.v` and `nngnum.v` (both subsumed by `signed.v`)
- in `topology.v`:
  + `ltr_distlC`, `ler_distlC`

### Infrastructure

### Misc
