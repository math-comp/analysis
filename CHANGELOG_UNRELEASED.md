# Changelog (unreleased)

## [Unreleased]

### Added

- in `normedtype.v`, lemmas `ereal_nbhs'_le`, `ereal_nbhs'_le_finite`

- in `normedtype.v`, lemmas `ball_open`

- in `normedtype.v`, definition `closed_ball_`, lemmas `closed_closed_ball_`

- in `normedtype.v`, definition `closed_ball`, lemmas `closed_ballxx`, `closed_ballE`,
  `closed_ball_closed`, `closed_ball_subset`, `nbhs_closedballP`, `subset_closed_ball`

- in `normedtype.v`, lemmas `nbhs0_lt`, `nbhs'0_lt`, `interior_closed_ballE`, open_nbhs_closed_ball`
- in `classical_sets.v`, lemmas `subset_has_lbound`, `subset_has_ubound`

- in `classical_sets.v`, lemma `mksetE`

- in `classical_sets.v`:
  + definitions `cover`, `partition`, `pblock_index`, `pblock`
  + lemmas `trivIsetP`, `trivIset_sets`, `trivIset_restr`, `perm_eq_trivIset`
  + lemma `fdisjoint_cset`

- in `reals.v`, lemmas `sup_setU`, `inf_setU`
- in `boolp.v`, lemmas `iff_notr`, `iff_not2`
- in `reals.v`, lemmas `RtointN`, `floor_le0`
- in `reals.v`, definition `Rceil`, lemmas `isint_Rceil`, `Rceil0`, `le_Rceil`,
  `Rceil_le`, `Rceil_ge0`
- in `reals.v`, definition `ceil`, lemmas `RceilE`, `ceil_ge0`, `ceil_le0`

- in `ereal.v`, lemmas `esum_fset_ninfty`, `esum_fset_pinfty`, `esum_pinfty`
- in `classical_sets.v`, lemmas `setDT`, `set0D`, `setD0`
- in `classical_sets.v`, lemmas `setC_bigcup`, `setC_bigcap`

- in `measure.v`, definition `sigma_finite`

- in `normedtype.v`: section "LinearContinuousBounded"
  + lemmas `linear_boundedP`, `linear_continuous0`, `linear_bounded0`,
    `continuousfor0_continuous`, `linear_bounded_continuous`, `bounded_funP`
  
### Changed

- header in `normedtype.v`, precisions on `bounded_fun`
- in `reals.v`:
  + `floor_ge0` generalized and renamed to `floorR_ge_int`
- in `ereal.v`, `ereal_scope` notation scope:
  + `x <= y` notation changed to `lee (x : er _) (y : er _)` and
    `only printing` notation `x <= y` for `lee x y`
  + same change for `<`
  + change extended to notations `_ <= _ <= _`, `_ < _ <= _`, `_ <= _ < _`, `_ < _ < _`

- in `classical_sets.v`:
  + generalization and change of `trivIset` (and thus lemmas `trivIset_bigUI` and `trivIset_setI`)

### Renamed

- in `normedtype.v`, `bounded_on` -> `bounded_near`

- in `topology.v`, `ball_ler` -> `le_ball`
- in `reals.v`:
  + `floor` -> `Rfloor`
  + `isint_floor` -> `isint_Rfloor`
  + `floorE` -> `RfloorE`
  + `mem_rg1_floor` -> `mem_rg1_Rfloor`
  + `floor_ler` -> `Rfloor_ler`
  + `floorS_gtr` -> `RfloorS_gtr`
  + `floor_natz` -> `Rfloor_natz`
  + `Rfloor` -> `Rfloor0`
  + `floor1` -> `Rfloor1`
  + `ler_floor` -> `ler_Rfloor`
  + `floor_le0` -> `Rfloor_le0`
  + `ifloor` -> `floor`
  + `ifloor_ge0` -> `floor_ge0`

- in `measure.v`:
  + `AdditiveMeasure.Measure` -> `AdditiveMeasure.Axioms`
  + `OuterMeasure.OuterMeasure` -> `OuterMeasure.Axioms`

### Removed

- in `topology.v`:
  + `ball_le`
- in `classical_sets.v`, lemma `bigcapCU`

- in `sequences.v`, lemmas `ler_sum_nat`, `sumr_const_nat`

### Infrastructure

### Misc
