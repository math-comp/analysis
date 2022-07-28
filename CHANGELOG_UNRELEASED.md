# Changelog (unreleased)

## [Unreleased]

### Added

- in file `boolp.v`:
  + lemmas `iter_compl`, `iter_compr`, `iter0`
- in file `functions.v`:
  + lemmas `oinv_iter`, `some_iter_inv`, `inv_iter`,
  + Instances for functions interfaces for `iter` (partial inverse up to 
      bijective function) 
- in `ereal.v`:
  + notations `_ < _ :> _` and `_ <= _ :> _`
  + lemmas `lee01`, `lte01`, `lee0N1`, `lte0N1`
  + lemmas `lee_pmul2l`, `lee_pmul2r`, `lte_pmul`, `lee_wpmul2l`
  + lemmas `lee_lt_add`, `lee_lt_dadd`, `lee_paddl`, `lee_pdaddl`,
    `lte_paddl`, `lte_pdaddl`, `lee_paddr`, `lee_pdaddr`,
    `lte_paddr`, `lte_pdaddr`
- in `lebesgue_integral.v`:
  + lemma `ge0_emeasurable_fun_sum`
  + lemma `integrableMr`
- in `ereal.v`:
  + lemmas `muleCA`, `muleAC`, `muleACA`
- in `classical_sets.v`:
  + lemma `preimage10P`
- in `classical_sets.v`:
  + lemma `setT_unit`

### Changed

- in `ereal.v`:
  + generalize `lee_pmul`
  + simplify `lte_le_add`, `lte_le_dadd`, `lte_le_sub`, `lte_le_dsub`
- in `measure.v`:
  + generalize `pushforward`
- in `lebesgue_integral.v`
  + change `Arguments` of `eq_integrable`
- in `lebesgue_integral.v`:
  + fix pretty-printing of `{mfun _ >-> _}`, `{sfun _ >-> _}`, `{nnfun _ >-> _}`
- in `lebesgue_integral.v`
  + minor generalization of `eq_measure_integral`
- in `topology.v`:
  + generalize `ltr_bigminr` to `porderType`
  + generalize `bigminr_ler` to `orderType`
- moved out of module `Bigminr` in `normedtype.v` to `topology.v` and generalizes to `orderType`:
  + lemma `bigminr_ler_cond`
- moved out of module `Bigminr` in `normedtype.v` and generalized to `orderType`:
  + lemma `bigminr_mkcond`, `bigminr_split`, `bigminr_idl`, `bigminrID`

bigminr_mkcond

### Renamed

- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `classical_sets.v`:
  + `set_bool` -> `setT_bool`

### Removed

- in `normedtype.v`
  + `Bigminr.bigminr_ler_cond`, `Bigminr.bigminr_ler`

### Infrastructure

### Misc
