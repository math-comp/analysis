# Changelog (unreleased)

## [Unreleased]

### Added

- in file `normedtype.v`,
  + new definition `type` (in module `completely_regular_uniformity`)
  + new lemmas `normal_completely_regular`, `completely_reg_opc`,
    `nbhs_opc_weakE`, `locally_compact_completely_regular`, and
    `completely_regular_regular`.

- in file `topology.v`,
  + new definitions `one_point_compactification`, and `one_point_nbhs`.
  + new lemmas `compact_normal_local`, `compact_normal`, `opc_compact`,
    `opc_some_nbhs`, `opc_some_continuous`, `opc_open_some`,
    `opc_weak_topology`, and `opc_hausdorff`.

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
