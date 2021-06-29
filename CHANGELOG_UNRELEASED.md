# Changelog (unreleased)

## [Unreleased]

### Added

- in `sequences.v`:
  + lemma `dvg_harmonic`
- in `topology.v`:
  + lemma `fmap_comp`
  + definition `patch`
  + notation `restrict`
  + definition `restrict_dep`
  + definition `extend_dep`
  + definition `fun_eq_on`
  + lemma `extend_restrict_dep`
  + lemma `restrict_extend_dep`
  + lemma `restrict_dep_restrict`
  + lemma `restrict_dep_setT`
  + lemma `forall_sigP`
  + definition `fct_RestrictedUniformTopology`
  + lemma `restricted_nbhs`
  + notation `{uniform A -> V }`
  + notation `{uniform A, F --> f }`
  + lemma `restricted_cvgE`
  + definition `fct_PointwiseTopology`
  + notation `{ptws U -> V}`
  + notation `{ptws F --> f }`
  + lemma `ptws_cvgE`
  + lemma `ptws_uniform_cvg`
  + lemma `fun_eq_onP`
  + lemma `cvg_restrict_dep`
  + lemma `eq_on_close`
  + lemma `hausdorrf_close_eq_on`
  + lemma `restricted_subset_nbhs`
  + lemma `restricted_subset_cvg`
  + lemma `restricted_restrict_cvg`
  + lemma `cvg_restrictedU`
  + lemma `cvg_restricted_set0`
  + definition `family_cvg_topologicalType`
  + notation `{family fam, U -> V}`
  + notation `{family fam, F --> f}`
  + lemma `fam_cvgP`
  + lemma `fam_cvgE`
  + definition `compactly_in`
  + lemma `family_cvg_subset`
  + lemma `family_cvg_finite_covers`
  + lemma `compact_cvg_within_compact`
- in `classical_set.v`
  + lemma `bigcup_setU1`
  + lemma `bigcap_setU1`
  + lemmas `seriesN`, `seriesD`, `seriesZ`, `is_cvg_seriesN`, `lim_seriesN`,
    `is_cvg_seriesZ`, `lim_seriesZ`, `is_cvg_seriesD`, `lim_seriesD`,
    `is_cvg_seriesB`, `lim_seriesB`, `lim_series_le`, `lim_series_norm`

### Changed

- in `measure.v`:
  + generalize lemma `eq_bigcupB_of`
- in `ereal.v`, definition `adde_undef` changed to `adde_def`
  + consequently, the following lemmas changed:
    * in `ereal.v`, `adde_undefC` renamed to `adde_defC`,
      `fin_num_adde_undef` renamed to `fin_num_adde_def`
    * in `sequences.v`, `ereal_cvgD` and `ereal_limD` now use hypotheses with `adde_def`
- in `sequences.v`:
  + generalize `{in,de}creasing_seqP`, `non{in,de}creasing_seqP` from `numDomainType`
    to `porderType`

### Renamed

### Removed

### Infrastructure

### Misc
