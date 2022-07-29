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
- in `mathcomp_extra.v`:
  + lemma `big_const_idem`
  + lemma `big_id_idem`
  + lemma `big_rem_AC`
  + lemma `bigD1_AC`
  + lemma `big_mkcond_idem`
  + lemma `big_split_idem`
  + lemma `big_id_idem_AC`
  + lemma `bigID_idem`
- in `mathcomp_extra.v`:
  + lemmas `bigmax_le` and `bigmax_lt`
  + lemma `bigmin_idr`
  + lemma `bigmax_idr`

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
- from `topology.v` to `mathcomp_extra.v`:
  + generalize `ltr_bigminr` to `porderType` and rename to `bigmin_lt`
  + generalize `bigminr_ler` to `orderType` and rename to `bigmin_le`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v` and generalized to `orderType`:
  + lemma `bigminr_ler_cond`, renamed to `bigmin_le_cond`
- moved out of module `Bigminr` in `normedtype.v` to `mathcomp_extra.v`:
  + lemma `bigminr_maxr`
- moved from from module `Bigminr` in `normedtype.v`
  + to `mathcomp_extra.v` and generalized to `orderType`
    * `bigminr_mkcond` -> `bigmin_mkcond`
    * `bigminr_split` -> `bigmin_split`
    * `bigminr_idl` -> `bigmin_idl`
    * `bigminrID` -> `bigminID`
    * `bigminrD1` -> `bigminD1`
    * `bigminr_inf` -> `bigmin_inf`
    * `bigminr_gerP` -> `bigmin_geP`
    * `bigminr_gtrP` -> ``bigmin_gtP``
    * `bigminr_eq_arg` -> `bigmin_eq_arg`
    * `eq_bigminr` -> `eq_bigmin`
  + to `topology.v` and generalized to `orderType`
    * `bigminr_lerP` -> `bigmin_leP`
    * `bigminr_ltrP` -> `bigmin_ltP`
- moved from `topology.v` to `mathcomp_extra.v`:
  + `bigmax_lerP` -> `bigmax_leP`
  + `bigmax_ltrP` -> `bigmax_ltP`
  + `ler_bigmax_cond` -> `le_bigmax_cond`
  + `ler_bigmax` -> `le_bigmax`
  + `le_bigmax` -> `homo_le_bigmax`

### Renamed

- in `ereal.v`:
  + `lee_pinfty_eq` -> `leye_eq`
  + `lee_ninfty_eq` -> `leeNy_eq`
- in `classical_sets.v`:
  + `set_bool` -> `setT_bool`
- in `topology.v`:
  + `bigmax_gerP` -> `bigmax_geP`
  + `bigmax_gtrP` -> `bigmax_gtP`

### Removed

- in `normedtype.v` (module `Bigminr`)
  + `bigminr_ler_cond`, `bigminr_ler`.
  + `bigminr_seq1`, `bigminr_pred1_eq`, `bigminr_pred1`
- in `topology.v`:
  + `bigmax_seq1`, `bigmax_pred1_eq`, `bigmax_pred1`

### Infrastructure

### Misc

- file `ereal.v` split in two files `constructive_ereal.v` and
  `ereal.v` (the latter exports the former, so the "Require Import
  ereal" can just be kept unchanged)
