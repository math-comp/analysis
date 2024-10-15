# Changelog (unreleased)

## [Unreleased]

### Added

- in file `normedtype.v`,
  + new definition `type` (in module `completely_regular_uniformity`)
  + new lemmas `normal_completely_regular`, and
    `locally_compact_completely_regular`.
  + new definition `type`.
  + new lemmas `normal_completely_regular`,
    `one_point_compactification_completely_reg`,
    `nbhs_one_point_compactification_weakE`,
    `locally_compact_completely_regular`, and
    `completely_regular_regular`.

- in file `topology.v`,
  + new definitions `one_point_compactification`, and `one_point_nbhs`.
  + new lemmas `compact_normal_local`, and `compact_normal`.
  + new lemmas `one_point_compactification_compact`,
    `one_point_compactification_some_nbhs`,
    `one_point_compactification_some_continuous`,
    `one_point_compactification_open_some`,
    `one_point_compactification_weak_topology`, and
    `one_point_compactification_hausdorff`.
- in file `separation_axioms.v`
  + new lemmas `compact_normal_local` and `compact_normal`.

### Changed

- in file `normedtype.v`,
     changed `completely_regular_space` to depend on uniform separators
     which removes the dependency on R.  The old formulation can be
     recovered easily with uniform_separatorP.

### Renamed

### Generalized

- in file `filter.v` generalized `smallest_filter_finI`.

### Deprecated

### Removed

### Infrastructure

### Misc
