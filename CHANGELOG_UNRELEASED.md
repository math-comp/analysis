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
- in `convex.v`:
  + lemmas `conv_gt0`, `convRE`

- in `exp.v`:
  + lemmas `concave_ln`, `conjugate_powR`

- in file `lebesgue_integral.v`,
  + new lemmas `integral_le_bound`, `continuous_compact_integrable`, and 
    `lebesgue_differentiation_continuous`.

- in `normedtype.v`:
  + lemmas `open_itvoo_subset`, `open_itvcc_subset`

- in `lebesgue_measure.v`:
  + lemma `measurable_ball`

- in file `normedtype.v`,
  + new lemmas `normal_openP`, `uniform_regular`,
    `regular_openP`, and `pseudometric_normal`.
- in file `topology.v`,
  + new definition `regular_space`.
  + new lemma `ent_closure`.

- in `lebesgue_measure.v`:
  + lemma `measurable_mulrr`

- in `constructive_ereal.v`:
  + lemma `eqe_pdivr_mull`

- new file `hoelder.v`:
  + definition `Lnorm`, notations `'N[mu]_p[f]`, `'N_p[f]`
  + lemmas `Lnorm1`, `Lnorm_ge0`, `eq_Lnorm`, `Lnorm_eq0_eq0`
  + lemma `hoelder`

- in file `lebesgue_integral.v`,
  + new lemmas `simple_bounded`, `measurable_bounded_integrable`, 
    `compact_finite_measure`, `approximation_continuous_integrable`

- in `sequences.v`:
  + lemma `cvge_harmonic`

- in `mathcomp_extra.v`:
  + lemmas `le_bigmax_seq`, `bigmax_sup_seq`

- in `constructive_ereal.v`:
  + lemma `bigmaxe_fin_num`
- in `ereal.v`:
  + lemmas `uboundT`, `supremumsT`, `supremumT`, `ereal_supT`, `range_oppe`,
    `ereal_infT`

- in `measure.v`:
  + definition `ess_sup`, lemma `ess_sup_ge0`

- in `exp.v`:
  + lemma `gt0_ltr_powR`
  + lemma `powR_injective`

### Changed

- `mnormalize` moved from `kernel.v` to `measure.v` and generalized
- in `constructive_ereal.v`:
  + `lee_adde` renamed to `lee_addgt0Pr` and turned into a reflect
  + `lee_dadde` renamed to `lee_daddgt0Pr` and turned into a reflect
- in `lebesgue_integral.v`
  + rewrote `negligible_integral` to replace the positivity condition
    with an integrability condition, and added `ge0_negligible_integral`.

- removed dependency in `Rstruct.v` on `normedtype.v`:
- added dependency in `normedtype.v` on `Rstruct.v`:

- in `cardinality.v`:
  + implicits of `fimfunP`

- in `lebesgue_integral.v`:
  + implicits of `integral_le_bound`

- in `measure.v`:
  + implicits of `measurable_fst` and `measurable_snd`
- in `exp.v`:
  + `gt0_ler_powR` now uses `Num.nneg`

### Renamed

- in `normedtype.v`: 
  + `normal_urysohnP` -> `normal_separatorP`.

- in `constructive_ereal.v`:
  + `lee_opp` -> `leeN2`
  + `lte_opp` -> `lteN2`

- in `exp.v`:
  + `gt0_ler_powR` -> `ge0_ler_powR`

### Generalized

### Deprecated

### Removed

- in `signed.v`:
  + specific notation for `2%:R`,
    now subsumed by number notations in MC >= 1.15
    Note that when importing ssrint, `2` now denotes `2%:~R` rather than `2%:R`,
    which are convertible but don't have the same head constant.

### Infrastructure

### Misc
