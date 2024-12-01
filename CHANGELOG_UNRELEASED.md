# Changelog (unreleased)

## [Unreleased]

### Added

- in `mathcomp_extra.v`
  + lemmas `comparable_BSide_min`, `BSide_min`, `BSide_max`,
    `real_BSide_min`, `real_BSide_max`, `natr_min`, `natr_max`,
    `comparable_min_le_min`, `comparable_max`, `min_le_min`,
    `max_le_max` and `real_sqrtC`

- in `itv.v`
  + lemmas `cmp0`, `neq0`, `eq0F`
  + definitions `ItvReal` and `Itv01`
  + lemmas `cmp0`, `neq0`, `eq0F`, `num_min`, `num_max`
  + notation `%:num`
  + notations `{posnum R}`, `{nonneg R}`, `%:pos`, `%:nng`,
    `%:posnum`, `%:nngnum`, `[gt0 of _]`, `[lt0 of _]`, `[ge0 of _]`,
    `[le0 of _]`, `[cmp0 of _]`, `[neq0 of _]`
  + definitions `PosNum` and `NngNum`

- in `constructive_ereal.v`
  + lemmas `cmp0y`, `cmp0Ny`, `real_miney`, `real_minNye`,
    `real_maxey`, `real_maxNye`, `oppe_cmp0`, `real_fine`,
    `real_muleN`, `real_mulNe`, `real_muleNN`

### Changed
  
- in `itv.v`
  + definition `ItvNum`

### Renamed

- in `itv.v`
  + `itv_bottom` -> `bottom`
  + `itv_gt0` -> `gt0`
  + `itv_le0F` -> `le0F`
  + `itv_lt0` -> `lt0`
  + `itv_ge0F` -> `ge0F`
  + `itv_ge0` -> `ge0`
  + `itv_lt0F` -> `lt0F`
  + `itv_le0` -> `le0`
  + `itv_gt0F` -> `gt0F`
  + `itv_top_typ` -> `top_typ`
  + `inum_eq` -> `num_eq`
  + `inum_le` -> `num_le`
  + `inum_lt` -> `num_lt`

### Generalized

- in `constructive_ereal.v`:
  + generalized from `realDomainType` to `numDomainType`
    * lemmas `EFin_min` and `EFin_max`
    * lemmas `maxye`, `maxeNy`, `mineNy`, `minye`

### Deprecated

- file `signed.v` (use `itv.v` instead)

- in `itv.v`:
  + notation `%:inum` (use `%:num` instead)

### Removed

### Infrastructure

### Misc
