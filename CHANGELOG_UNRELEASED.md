# Changelog (unreleased)

## [Unreleased]

### Added

- in `boolp.v`:
  + lemma `not_andP`
- in `classical_sets.v`:
  + lemmas `setIIl`, `setIIr`, `setCS`, `setSD`, `setDS`, `setDSS`, `setCI`,
    `setDUr`, `setDUl`, `setIDA`, `setDD`
- in `normedtype.v`:
  + lemma `closed_ereal_le_ereal`
  + lemma `closed_ereal_ge_ereal`
  + lemmas `set0M`, `setM0`, `image_set0_set0`, `subset_set1`, `preimage_set0`

### Changed

- in `classical_sets.v`:
  + the index in `bigcup_set1` generalized from `nat` to some `Type`
- lemma `asboolb` moved from `discrete.v` to `boolp.v`
- lemma `exists2NP` moved from `discrete.v` to `boolp.v`
- lemma `neg_or` moved from `discrete.v` to `boolp.v` and renamed to `not_orP`

### Renamed

- in `classical_sets.v`:
  + `setIDl` -> `setIUl`
  + `setUDl` -> `setUIl`
  + `setUDr` -> `setUIr`
  + `setIDr` -> `setIUl`
- in `boolp.v`:
  + `contrap` -> `contra_not`
  + `contrapL` -> `contraPnot`
  + `contrapR` -> `contra_notP`
  + `contrapLR` -> `contraPP`

### Removed

- in `boolp.v`:
  + `contrapNN`, `contrapTN`, `contrapNT`, `contrapTT`
  + `eqNN`
- in `normedtype.v`:
  + `forallN`
  + `eqNNP`
  + `existsN`
- in `discrete.v`:
  + `existsP`
  + `existsNP`

### Infrastructure

### Misc
