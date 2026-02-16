# Changelog (unreleased)

## [Unreleased]

### Added
- in classical_sets.v
  + lemma `powerset0`, `powerset1`, `powerset2`, `powersetS`,
    `setorder_itv_setUl_image`, `setorder_itv_setUr_image`,
    `setorder_itv_setDl_image`

- in set_interval.v
  + lemmas `itv_open_endsPn`, `itv_closed_endsPn`, `itv_open_ends_boundlr`,
    `setUitv2`, `setDitv2`, `setDitvoo`, `setDitvoy`, `setDitvNyo`,
    `setDccitv`, `setDcitvy`, `setDcitvNy`

- in topology_structure.v
  + lemmas `closureEbigcap_itvcy`,`interiorEbigcup_itvNyc`,
    `closureEbigcap_itvcc`,`interiorEbigcup_itvcc`

- in num_topology.v
  + lemmas `open_itv_open_ends`, `closed_itv_closed_ends`,
    `itv_closureE`, `itv_interiorE`

- in order_topology.v
  + lemma `itv_closed_ends_closed`
- in classical_sets.v
  + lemma `in_set1_eq`

- in `sequences.v`:
  + lemma `sdrop_shift`
  + lemma `ge_einfs`
  + lemma `einfs_shift`
  + lemma `limn_einf_shift_new`
  + lemma `limn_einf_shiftS`
  + lemma `limn_einf_cst`
- in `uniform_structure.v`:
  + lemma `unif_continuous_continuous`

### Changed
- in set_interval.v
  + `setDitv1l`, `setDitv1r` (generalized)

- in set_interval.v
  + `itv_is_closed_unbounded` (fix the definition)

- in `esum.v`:
  + level of notation `\esum_ ( i 'in' P ) F`
    from level 41 to 34

- in `lebesgue_integral_definition.v`
  + level of notation `\int[ mu ]_( i 'in' D) F`
    from level 36 to 34 and level of `F` from 36 to 41.
    In particular, this means that `\int[mu]_(x in D) f x * g x`
    now parses as `\int[mu]_(x in D) (f x * g x)`.

### Renamed

- in `sequences.v`:
  + `limn_einf_shift` -> `limn_einf_addl`

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
