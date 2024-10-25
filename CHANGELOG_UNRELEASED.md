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

- package `coq-mathcomp-experimental-reals` depending on `coq-mathcomp-reals`
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


### Changed

- in file `normedtype.v`,
     changed `completely_regular_space` to depend on uniform separators
     which removes the dependency on `R`.  The old formulation can be
     recovered easily with `uniform_separatorP`.

- moved from `Rstruct.v` to `Rstruct_topology.v`
  + lemmas `continuity_pt_nbhs`, `continuity_pt_cvg`,
    `continuity_ptE`, `continuity_pt_cvg'`, `continuity_pt_dnbhs`
    and `nbhs_pt_comp`

- moved from `real_interval.v` to `normedtype.v`
  + lemmas `set_itvK`, `RhullT`, `RhullK`, `set_itv_setT`,
    `Rhull_smallest`, `le_Rhull`, `neitv_Rhull`, `Rhull_involutive`,
    `disj_itv_Rhull`
- in `topology.v`:
  + lemmas `subspace_pm_ball_center`, `subspace_pm_ball_sym`,
    `subspace_pm_ball_triangle`, `subspace_pm_entourage` turned
	into local `Let`'s

- in `lebesgue_integral.v`:
  + structure `SimpleFun` now inside a module `HBSimple`
  + structure `NonNegSimpleFun` now inside a module `HBNNSimple`
  + lemma `cst_nnfun_subproof` has now a different statement
  + lemma `indic_nnfun_subproof` has now a different statement
- in `mathcomp_extra.v`:
  + definition `idempotent_fun`

- in `topology_structure.v`:
  + definitions `regopen`, `regclosed`
  + lemmas `interiorC`, `closureU`, `interiorU`,
           `closureEbigcap`, `interiorEbigcup`,
	   `closure_open_regclosed`, `interior_closed_regopen`,
	   `closure_interior_idem`, `interior_closure_idem`

### Changed

- in `topology_structure.v`:
  + lemma `closureC`

### Renamed

### Generalized

- in `lebesgue_integral.v`:
  + generalized from `sigmaRingType`/`realType` to `sigmaRingType`/`sigmaRingType`
    * mixin `isMeasurableFun`
    * structure `MeasurableFun`
	* definition `mfun`
    * lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`

### Deprecated

### Removed

- in `lebesgue_integral.v`:
  + definition `cst_mfun`
  + lemma `mfun_cst`

- in `cardinality.v`:
  + lemma `cst_fimfun_subproof`

- in `lebesgue_integral.v`:
  + lemma `cst_mfun_subproof` (use lemma `measurable_cst` instead)
  + lemma `cst_nnfun_subproof` (turned into a `Let`)
  + lemma `indic_mfun_subproof` (use lemma `measurable_fun_indic` instead)

### Infrastructure

### Misc
