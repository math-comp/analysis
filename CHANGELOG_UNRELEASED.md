# Changelog (unreleased)

## [Unreleased]

### Added

- in `unstable.v`:
  + lemma `sqrtK`

- in `realfun.v`:
  + instance `is_derive1_sqrt`

- in `mathcomp_extra.v`:
  + lemmas `subrKC`, `sumr_le0`, `card_fset_sum1`

- in `functions.v`:
  + lemmas `fct_prodE`, `prodrfctE`

- in `exp.v`:
  + lemma `norm_expR`

- in `hoelder.v`
  + lemma `hoelder_conj_ge1`

- in `reals.v`:
  + definition `irrational`
  + lemmas `irrationalE`, `rationalP` 

- in `topology_structure.v`:
  + lemmas `denseI`, `dense0`

- in `pseudometric_normed_Zmodule.v`:
  + lemma `dense_set1C`

- new file `borel_hierarchy.v`:
  + definitions `Gdelta`, `Fsigma`
  + lemmas `closed_Fsigma`, `Gdelta_measurable`, `Gdelta_subspace_open`,
    `irrational_Gdelta`, `not_rational_Gdelta`

- in `constructive_ereal.v`:
  + lemma `expe0`, `mule0n`, `muleS`

- in `exp.v`:
  + lemmas `expeR_eqy`
  + lemmas `lt0_powR1`, `powR_eq1`
  + definition `lne`
  + lemmas `le0_lneNy`, `lne_EFin`, `expeRK`, `lneK`, `lneK_eq`, `lne1`, `lneM`, 
    `lne_inj`, `lneV`, `lne_div`, `lte_lne`, `lee_lne`, `lneXn`, `le_lne1Dx`, 
    `lne_sublinear`, `lne_ge0`, `lne_lt0`, `lne_gt0`, `lne_le0`
  + lemma `lne_eq0`

- in `charge.v`:
  + definition `copp`, lemma `cscaleN1`
- in `classical_orders.v`:
  + lemma `big_lexi_order_prefix_closed_itv`

### Changed

- moved from `pi_irrational.v` to `reals.v` and changed
  + definition `rational`

- in `constructive_ereal.v`:
  + lemma `mulN1e`

- in `measurable_realfun.v`:
  + generalized and renamed:
    * `measurable_fun_itv_bndo_bndc` -> `measurable_fun_itv_bndo_bndcP`
    * `measurable_fun_itv_obnd_cbnd` -> `measurable_fun_itv_obnd_cbndP`
- moved from `simple_functions.v` to `measure.v`
  + notations `{mfun _ >-> _}`, `[mfun of _]`
  + mixin `isMeasurableFun`, structure `MesurableFun`, lemmas `measurable_funP`, `measurable_sfunP`
  + definitions `mfun`, `mfun_key`, canonical `mfun_keyed`
  + definitions `mfun_Sub_subproof`, `mfun_Sub`
  + lemmas `mfun_rect`, `mfun_valP`, `mfuneqP`
  + lemma `measurableT_comp_subproof`

- moved from `simple_functions.v` to `measurable_realfun.v`
  + lemmas `mfun_subring_closed`, `mfun0`, `mfun1`, `mfunN`,
    `mfunD`, `mfunB`, `mfunM`, `mfunMn`, `mfun_sum`, `mfun_prod`, `mfunX`
  + definitions `mindic`, `indic_mfun`, `scale_mfun`, `max_mfun`
  + lemmas `mindicE`, `max_mfun_subproof`

- moved from `simple_functions.v` to `lebesgue_stieltjes_measure.v`
  + lemma `measurable_sfun_inP`

### Renamed

- in `lebesgue_stieltjes_measure.v`:
  + `cumulativeNy0` -> `cumulativeNy`
  + `cumulativey1` -> `cumulativey`

- in `exp.v`:
  + `ltr_expeR` -> `lte_expeR`
  + `ler_expeR` -> `lee_expeR`

- in `derive.v`:
  + `derivemxE` -> `deriveEjacobian`

- `measurable_sfunP` -> `measurable_funPTI`
  (and moved from from `simple_functions.v` to `measure.v`)

- `measurable_sfun_inP` -> `measurable_funP1`
  (and moved from `simple_functions.v` to `lebesgue_stieltjes_measure.v`)

### Generalized

- in `functions.v`
  + lemma `fct_sumE` (from a pointwise equality to a functional one)

### Deprecated

### Removed

- file `forms.v` (superseded by MathComp's `sesquilinear.v`)

- in `simple_functions.v`:
  + duplicated hints about `measurable_set1`

### Infrastructure

### Misc
