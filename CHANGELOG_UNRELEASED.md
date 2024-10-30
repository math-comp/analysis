# Changelog (unreleased)

## [Unreleased]

### Added

- file `Rstruct_topology.v`

- package `coq-mathcomp-reals` depending on `coq-mathcomp-classical`
  with files
  + `constructive_ereal.v`
  + `reals.v`
  + `real_interval.v`
  + `signed.v`
  + `itv.v`
  + `prodnormedzmodule.v`
  + `nsatz_realtype.v`
  + `all_reals.v`

- in file `separation_axioms.v`,
  + new lemmas `compact_normal_local`, and `compact_normal`.

- package `coq-mathcomp-altreals` depending on `coq-mathcomp-reals`
  with files
  + `xfinmap.v`
  + `discrete.v`
  + `realseq.v`
  + `realsum.v`
  + `distr.v`

- package `coq-mathcomp-reals-stdlib` depending on `coq-mathcomp-reals`
  with file
  + `Rstruct.v`

- package `coq-mathcomp-analysis-stdlib` depending on
  `coq-mathcomp-analysis` and `coq-mathcomp-reals-stdlib` with files
  + `Rstruct_topology.v`
  + `showcase/uniform_bigO.v`

- in file `separation_axioms.v`,
  + new lemmas `compact_normal_local`, and `compact_normal`.

- in file `topology_theory/one_point_compactification.v`,
  + new definitions `one_point_compactification`, and `one_point_nbhs`.
  + new lemmas `one_point_compactification_compact`,
    `one_point_compactification_some_nbhs`,
    `one_point_compactification_some_continuous`,
    `one_point_compactification_open_some`,
    `one_point_compactification_weak_topology`, and
    `one_point_compactification_hausdorff`.

- in file `normedtype.v`,
  + new definition `type` (in module `completely_regular_uniformity`)
  + new lemmas `normal_completely_regular`,
    `one_point_compactification_completely_reg`,
    `nbhs_one_point_compactification_weakE`,
    `locally_compact_completely_regular`, and
    `completely_regular_regular`.

- in file `mathcomp_extra.v`,
  + new definition `sigT_fun`.
- in file `sigT_topology.v`,
  + new definition `sigT_nbhs`.
  + new lemmas `sigT_nbhsE`, `existT_continuous`, `existT_open_map`,
    `existT_nbhs`, `sigT_openP`, `sigT_continuous`, `sigT_setUE`, and 
    `sigT_compact`.
- in file `separation_axioms.v`,
  + new lemma `sigT_hausdorff`.

- in file `normedtype.v`,
  + new lemmas `continuous_within_itvcyP`, `continuous_within_itvycP`

### Changed
  
### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
