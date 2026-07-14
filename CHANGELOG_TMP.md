### Added

- in file `filter.v`,
  + new lemmas `near_eq_cvgE`, `near_eq_is_cvg`, `near_eq_lim`, 
    `cvg_to_eq`, `cvg_to_withinP`, and `within_cvg_to_within`.
- in file `derive.v`,
  + new lemmas `derive1Dn`, `der1_scaleLR`, `deriveZLR`, `derivableZLR`, 
    `derivable_shiftf`, `derive_shiftf`, `is_derive_shiftf`, `derive1_shiftf`, 
    `near_eq_derive1n_near`, `near_eq_derive1_near`, `near_eq_derive1n`, 
    `near_eq_derive1`, `right_derivative_limit`, `left_derivative_limit`, and 
    `dnbhs_derivative_limit`.
  + new theorem `derivative_limit_theorem`.
- in file `exp.v`,
  + new lemmas `cvgy_expR`, `cvgNy_expR`, `lny`, `Nlt1_powR_cvg0`, 
    `expMexpR_cvgr0`, `powRMexpR_cvgr0`, `expMpowR_cvgr0`, and 
    `expMexpr_cvgn0`.
- in file `ftc.v`,
  + new lemmas `continuous_FTC1_is_derive`, `continuous_FTC1y`, and 
    `continuous_near_pinfty_le_integrable`.
- in file `realfun.v`,
  + new lemmas `derivable_oo_LRcontinuousZ`, `derivable_oo_LRcontinuousD`, 
    `derivable_oo_LRcontinuousN`, `derivable_oo_LRcontinuous_shift`, 
    `derivable_oo_LRcontinuousS`, `lhopital_pinfty_at_right`, and 
    `lhopital_pinfty_at_pinfty`.
- in file `sequences.v`,
  + new lemmas `is_cvg_series_shiftn`, and `series_near_le_cvg`.

### Renamed


### Generalized


### Deprecated


### Maybe changed


### Moved from one file to another and maybe changed or generalized

- moved from `realfun.v` to `derive.v`: `is_deriveV`.

### Removed

