# Changelog (unreleased)

## [Unreleased]

### Added
- in `normedtype.v`:
  + definitions `contraction` and `is_contraction`
  + lemma `contraction_fixpoint_unique`
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
- in `topology.v`:
  + lemma `near_inftyS`
- in `sequences.v`:
  + definition `contraction`, `is_contraction`
  + lemmas `contraction_dist`, `contraction_cvg`,
    `contraction_cvg_fixed`, `banach_fixed_point`,
    `contraction_unique`

- in `constructive_ereal.v`:
  + lemmas `ltNye_eq`, `sube_lt0`, `subre_lt0`, `suber_lt0`, `sube_ge0`
  + lemmas `dsubre_gt0`, `dsuber_gt0`, `dsube_gt0`, `dsube_le0`

### Changed

### Renamed

- in `constructive_ereal.v`:
  + `lte_pinfty_eq` -> `ltey_eq`

### Removed

### Infrastructure

### Misc
