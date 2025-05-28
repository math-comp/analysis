# Changelog (unreleased)

## [Unreleased]

### Added

- in `unstable.v`:
  + lemma `subrKC`

- in `convex.v`:
  + definition `convex_quasi_associative`
    * implemented through a module `ConvexQuasiAssoc` containing
      `law` and helper lemmas
  + lemmas `convR_itv`, `convR_line_path`

### Changed

- in `convex.v`:
  + convex combination operator `a <| t |> b` changed from
    `(1-t)a + tb` to `ta + (1-t)b`

- in `sequences.v`:
  + lemma `subset_seqDU`

- in `measure.v`:
  + lemmas `seqDU_measurable`, `measure_gt0`
  + notations `\forall x \ae mu, P`, `f = g %[ae mu in D]`, `f = g %[ae mu]`
  + instances `ae_eq_equiv`, `comp_ae_eq`, `comp_ae_eq2`, `comp_ae_eq2'`, `sub_ae_eq2`
  + lemma `ae_eq_comp2`
  + lemma `ae_foralln`
  + lemma `ae_eqe_mul2l`

- new file `ess_sup_inf.v`:
  + lemma `measure0_ae`
  + definition `ess_esup`
  + lemmas `ess_supEae`, `ae_le_measureP`, `ess_supEmu0`, `ess_sup_ge`,
    `ess_supP`, `le_ess_sup`, `eq_ess_sup`, `ess_sup_cst`, `ess_sup_ae_cst`,
    `ess_sup_gee`, `abs_sup_eq0_ae_eq`, `abs_ess_sup_eq0`, `ess_sup_pZl`,
    `ess_supZl`, `ess_sup_eqNyP`, `ess_supD`, `ess_sup_absD`
  + notation `ess_supr`
  + lemmas `ess_supr_bounded`, `ess_sup_eqr0_ae_eq`, `ess_suprZl`,
    `ess_sup_ger`, `ess_sup_ler`, `ess_sup_cstr`, `ess_suprD`, `ess_sup_normD`
  + definition `ess_inf`
  + lemmas `ess_infEae`, `ess_infEN`, `ess_supEN`, `ess_infN`, `ess_supN`,
    `ess_infP`, `ess_inf_le`, `le_ess_inf`, `eq_ess_inf`, `ess_inf_cst`,
    `ess_inf_ae_cst`, `ess_inf_gee`, `ess_inf_pZl`, `ess_infZl`, `ess_inf_eqyP`,
    `ess_infD`
  + notation `ess_infr`
  + lemmas `ess_infr_bounded`, `ess_infrZl`, `ess_inf_ger`, `ess_inf_ler`,
    `ess_inf_cstr`

### Changed

- in `measure.v`:
  + notation `{ae mu, P}` (near use `{near _, _}` notation)
  + definition `ae_eq`
  + `ae_eq` lemmas now for `ringType`-valued functions (instead of `\bar R`)

- in `convex.v`:
  + definition `convex_realDomainType` generalized and
    renamed accordingly `convex_numDomainType`

### Renamed

- in `measure.v`
  + definition `ess_sup` moved to `ess_sup_inf.v`

- in `convex.v`
  + lemma `conv_gt0` to `convR_gt0`

### Generalized

- in `derive.v`:
  + `derive_cst`, `derive1_cst`
- in `convex.v`
  + parameter `R` of `convType` from `realDomainType` to `numDomainType`

### Deprecated

### Removed

- in `measure.v`:
  + definition `almost_everywhere_notation`
  + lemma `ess_sup_ge0`

### Infrastructure

### Misc
