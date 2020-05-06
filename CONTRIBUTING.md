# Contribution Guide for the mathcomp-analysis library (WIP)

## `=>` vs. `-->` vs. cvg vs. lim

TODO: explain in particular the lemmas `cvgP`, `cvg_ex`

## `near` tactics vs. `filterS`, `filterS2`, `filterS3` lemmas

TODO

## idioms

### How to introduce a positive real number?

When introducing a positive real number, it is best to turn it into a
`posnum` whose type is equipped with better automation. There is an
idiomatic way to perform such an introduction. Given a goal of the
form
```
==========================
forall e : R, 0 < e -> G
```
the tactic `move=> _/posnumP[e]` performs the following introduction
```
e : {posnum R}
==========================
G
```
