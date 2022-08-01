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
- in `classical_sets.v`:
  + lemma `subset_refl`
- in `normedtype.v`:
  + definitions `contraction` and `is_contraction`
  + lemma `contraction_fixpoint_unique`

### Changed

### Renamed

### Removed

### Infrastructure

### Misc
