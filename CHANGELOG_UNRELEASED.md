# Changelog (unreleased)

## [Unreleased]

### Added
 
- in `ereal.v`:
  + lemmas `big_nat_widenl`, `big_geq_mkord`
  + lemmas `lee_sum_nneg_natr`, `lee_sum_nneg_natl`
- in `sequences.v`:
  + notations `\sum_(i <oo) F i`
  + lemmas `ereal_pseries_sum_nat`, `lte_lim`
  + lemmas `is_cvg_ereal_nneg_natsum_cond`, `is_cvg_ereal_nneg_natsum`
  + lemma `ereal_pseriesD`, `ereal_pseries0`, `eq_ereal_pseries`
- in `classical_sets.v`, lemma `subset_bigsetU_cond`
- in `measure.v`:
  + lemma `eq_bigcupB_of_bigsetU`
  + definitions `caratheodory_type`
  + definition `caratheodory_measure` and lemma `caratheodory_measure_complete`
  + internal definitions and lemmas that may be deprecated and hidden in the future:
    * `caratheodory_measurable`, notation `... .-measurable`,
    * `le_caratheodory_measurable`, `outer_measure_bigcup_lim`,
      `caratheodory_measurable_{set0,setC,setU_le,setU,bigsetU,setI,setD}`
      `disjoint_caratheodoryIU`, `caratheodory_additive`,
          `caratheodory_lim_lee`, `caratheodory_measurable_trivIset_bigcup`,
      `caratheodory_measurable_bigcup`
- file `csum.v`:
  + lemmas `ereal_pseries_pred0`, `ub_ereal_sup_adherent_img`
  + definition `fsets`, lemmas `fsets_set0`, `fsets_self`, `fsetsP`, `fsets_img`
  + definition `fsets_ord`, lemmas `fsets_ord_nat`, `fsets_ord_subset`
  + definition `gsum`, lemmas `gsum0`, `gsumE`, `gsum_ge0`, `gsum_fset`
    `gsum_image`, `gsum_nat_lim`, `gsum_bigcup`
  + notation `\gsum_(i in S) a i`
- file `cardinality.v`
  + defintion `surjective`
  + definition `set_bijective`
  + definition `inverse`
  + notation `` `I_n ``
  + lemmas `pigeonhole`, `Cantor_Bernstein`
  + definition `card_le`, notation `_ #<= _`
  + definition `card_eq`, notation `_ #= _`
  + definition `countable`
  + definition `set_finite`
  + definitions `enumeration`, `enum_wo_rep`
  + lemmas `infinite_nat`, `infinite_prod_nat`

### Changed

- in `ereal.v`:
  + change implicits of lemma `lee_sum_nneg_ord`
- in `sequences.v`:
  + change implicits of lemma `is_cvg_ereal_nneg_series`
  + statements changed from using sum of ordinals to sum of nats
    * definition `series`
    * lemmas `ereal_nondecreasing_series`, `ereal_nneg_series_lim_ge`
    * lemmas `is_cvg_ereal_nneg_series_cond`, `is_cvg_ereal_nneg_series`
    * lemmas `ereal_nneg_series_lim_ge0`, `ereal_nneg_series_pinfty`
- in `classical_sets.v`, lemma `subset_bigsetU`

### Renamed

- in `sequences,v`:
  + `is_cvg_ereal_nneg_series_cond`

### Removed

### Infrastructure

### Misc
