# Changelog (unreleased)

## [Unreleased]

### Added

- file `mathcomp_extra.v`
  + lemmas `ge_trunc`, `lt_succ_trunc`, `trunc_ge_nat`, `trunc_lt_nat`

- file `Rstruct.v`
  + lemma `Pos_to_natE` (from `mathcomp_extra.v`)
  + lemmas `RabsE`, `RdistE`, `sum_f_R0E`, `factE`

- new file `internal_Eqdep_dec.v` (don't use, internal, to be removed)

- file `constructive_ereal.v`:
  + definition `iter_mule`
  + lemma `prodEFin`

- file `exp.v`:
  + lemma `expR_sum`

- file `lebesgue_integral.v`:
  + lemma `measurable_fun_le`

- in `trigo.v`:
  + lemma `integral0oo_atan`

- in `measure.v`:
  + lemmas `preimage_set_system0`, `preimage_set_systemU`, `preimage_set_system_comp`
  + lemma `preimage_set_system_id`

- in `Rstruct_topology.v`:
  + lemma `RexpE`

- in `derive.v`:
  + lemmas `derive_shift`, `is_derive_shift`

- in `mathcomp_extra.v`
  + lemmas `real_lt_succ_trunc`, `trunc_gt_nat`, `real_trunc_le_nat`,
    `trunc_eq`, `trunc_le`, `natrKtrunc`, `natrEtrunc`,
    `real_floor_ge_int_tmp`, `real_floor_ge_int`, `real_floor_lt_int`,
    `real_floor_eq`, `real_floor_ge0`, `real_floor_le0`, `floor_gt0`,
    `real_abs_floor_ge`, `real_ceil_le_int_tmp`, `real_ceil_le_int`,
    `real_ceil_gt_int`, `real_ceil_eq`, `real_ceil_ge0`, `ceil_lt0`,
    `real_ceil_le0`, `ceil_neq0`, `real_abs_ceil_ge`, `trunc_le_nat`,
    `floor_ge_int_tmp`, `abs_floor_ge`, `ceil_le_int`,
    `ceil_le_int_tmp`

### Changed

- file `nsatz_realtype.v` moved from `reals` to `reals-stdlib` package
- moved from `gauss_integral` to `trigo.v`:
  + `oneDsqr`, `oneDsqr_ge1`, `oneDsqr_inum`, `oneDsqrV_le1`,
    `continuous_oneDsqr`, `continuous_oneDsqr`
- moved, generalized, and renamed from `gauss_integral` to `trigo.v`:
  + `integral01_oneDsqr` -> `integral0_oneDsqr`

- in `mathcomp_extra.v`:
  + `floor_lt_int`, `floor_le0`, `floor_lt0`, `ceil_gt_int`,
    `ceil_ge0`, `ceil_le0`, `ceil_gt0` (equality direction)

### Renamed

- in `lebesgue_integral.v`:
  + `fubini1a` -> `integrable12ltyP`
  + `fubini1b` -> `integrable21ltyP`
  + `measurable_funP` -> `measurable_funPT` (field of `isMeasurableFun` mixin)

- in `mathcomp_extra.v`
  + `comparable_min_le_min` -> `comparable_le_min2`
  + `comparable_max_le_max` -> `comparable_le_max2`
  + `min_le_min` -> `le_min2`
  + `max_le_max` -> `le_max2`
  + `real_sqrtC` -> `sqrtC_real`
  + `intrD1` -> `intr1`
  + `intr1D` -> `int1r`
  + `nat_int` -> `natr_int`

### Generalized

- in `constructive_ereal.v`:
  + lemma `EFin_natmul`

- in `lebesgue_integral.v`
  + lemmas `measurable_funP`, `ge0_integral_pushforward`,
    `integrable_pushforward`, `integral_pushforward`

- in `mathcomp_extra.v`
  + lemmas `ge_trunc`, `trunc_ge_nat`, `floor_lt0`, `floor_neq0`,
    `ceil_gt0` (from `archiRealDomainType` to `archiNumDomainType`)

### Deprecated

- in `mathcomp_extra.v`
  + `intrD1` (renamed `intr1`)
  + `intr1D` (renamed `int1r`)
  + `nat_int` (renamed `natr_int`)
  + `real_floor_ge_int` (use `real_floor_ge_int_tmp` instead)
  + `floor_ge_int` (use `floor_ge_int_tmp` instead)

### Removed

- file `mathcomp_extra.v`
  + lemma `Pos_to_natE` (moved to `Rstruct.v`)
  + lemma `deg_le2_ge0` (available as `deg_le2_poly_ge0` in `ssrnum.v`
    since MathComp 2.1.0)

### Infrastructure

### Misc
