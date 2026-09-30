# Changelog (unreleased)

## [Unreleased]

### Added

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
