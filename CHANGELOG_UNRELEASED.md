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
  + new lemmas `near_in_itvoy`, `near_in_itvNyo`

- in file `mathcomp_extra.v`,
  + new definition `sigT_fun`.
- in file `sigT_topology.v`,
  + new definition `sigT_nbhs`.
  + new lemmas `sigT_nbhsE`, `existT_continuous`, `existT_open_map`,
    `existT_nbhs`, `sigT_openP`, `sigT_continuous`, `sigT_setUE`, and 
    `sigT_compact`.
- in file `separation_axioms.v`,
  + new lemma `sigT_hausdorff`.

- in `measure.v`:
  + lemma `countable_measurable`
- in `realfun.v`:
  + lemma `cvgr_dnbhsP`
  + new definitions `prodA`, and `prodAr`.
  + new lemmas `prodAK`, `prodArK`, and `swapK`.
- in file `product_topology.v`,
  + new lemmas `swap_continuous`, `prodA_continuous`, and 
    `prodAr_continuous`.

- file `homotopy_theory/homotopy.v`
- file `homotopy_theory/wedge_sigT.v`
- in file `homotopy_theory/wedge_sigT.v`
  + new definitions `wedge_rel`, `wedge`, `wedge_lift`, `pwedge`.
  + new lemmas `wedge_lift_continuous`, `wedge_lift_nbhs`,
    `wedge_liftE`, `wedge_openP`,
    `wedge_pointE`, `wedge_point_nbhs`, `wedge_nbhs_specP`, `wedgeTE`,
    `wedge_compact`, `wedge_connected`.

- in `boolp.`:
  + lemma `existT_inj2`
- in file `order_topology.v`
  + new lemmas `min_continuous`, `min_fun_continuous`, `max_continuous`, and
    `max_fun_continuous`.

- in file `boolp.v`,
  + new lemmas `uncurryK`, and `curryK`
- in file `weak_topology.v`,
  + new lemma `continuous_comp_weak`
- in file `function_spaces.v`,
  + new definition `eval`
  + new lemmas `continuous_curry_fun`, `continuous_curry_cvg`, 
    `eval_continuous`, and `compose_continuous`

- in file `wedge_sigT.v`,
+ new definitions `wedge_fun`, and `wedge_prod`.
+ new lemmas `wedge_fun_continuous`, `wedge_lift_funE`, 
  `wedge_fun_comp`, `wedge_prod_pointE`, `wedge_prod_inj`, 
  `wedge_prod_continuous`, `wedge_prod_open`, `wedge_hausdorff`, and 
  `wedge_fun_joint_continuous`.

- in `boolp.v`:
  + lemmas `existT_inj1`, `surjective_existT`

- in file `homotopy_theory/path.v`,
  + new definitions `reparameterize`, `mk_path`, and `chain_path`.
  + new lemmas `path_eqP`, and `chain_path_cts_point`.
- in file `homotopy_theory/wedge_sigT.v`,
  + new definition `bpwedge_shared_pt`.
  + new notations `bpwedge`, and `bpwedge_lift`.

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
  + lemmas `closure_setC`, `interiorC`, `closureU`, `interiorU`,
           `closureEbigcap`, `interiorEbigcup`,
	   `closure_open_regclosed`, `interior_closed_regopen`,
	   `closure_interior_idem`, `interior_closure_idem`

- in file `topology_structure.v`,
  + mixin `isContinuous`, type `continuousType`, structure `Continuous`
  + new lemma `continuousEP`.
  + new definition `mkcts`.

- in file `subspace_topology.v`,
  + new lemmas `continuous_subspace_setT`, `nbhs_prodX_subspace_inE`, and
    `continuous_subspace_prodP`.
  + type `continuousFunType`, HB structure `ContinuousFun`

- in file `subtype_topology.v`,
  + new lemmas `subspace_subtypeP`, `subspace_sigL_continuousP`,
    `subspace_valL_continuousP'`, `subspace_valL_continuousP`, `sigT_of_setXK`,
    `setX_of_sigTK`, `setX_of_sigT_continuous`, and `sigT_of_setX_continuous`.

- in `tvs.v`:
  + HB structures `NbhsNmodule`, `NbhsZmodule`, `NbhsLmodule`, `TopologicalNmodule`,
    `TopologicalZmodule`
  + notation `topologicalLmoduleType`, HB structure `TopologicalLmodule`
  + HB structures `UniformZmodule`, `UniformLmodule`
  + definition `convex`
  + mixin `Uniform_isTvs`
  + type `tvsType`, HB.structure `Tvs`
  + HB.factory `TopologicalLmod_isTvs`
  + lemma `nbhs0N`
  + lemma `nbhsN`
  + lemma `nbhsT`
  + lemma `nbhsB`
  + lemma `nbhs0Z`
  + lemma `nbhZ`
  
### Changed

- in normedtype.v
  + HB structure `normedModule` now depends on a Tvs
    instead of a Lmodule
  + Factory `PseudoMetricNormedZmod_Lmodule_isNormedModule` becomes
    `PseudoMetricNormedZmod_Tvs_isNormedModule`
  + Section `prod_NormedModule` now depends on a `numFieldType`
  
### Renamed

- in `normedtype.v`:
  + `near_in_itv` -> `near_in_itvoo`

- in normedtype.v
  + Section `regular_topology` to `standard_topology`
  
### Generalized

- in `lebesgue_integral.v`:
  + generalized from `sigmaRingType`/`realType` to `sigmaRingType`/`sigmaRingType`
    * mixin `isMeasurableFun`
    * structure `MeasurableFun`
	* definition `mfun`
    * lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`

### Deprecated

- in `topology_structure.v`:
  + lemma `closureC`

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
