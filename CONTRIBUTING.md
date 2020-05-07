# Contribution Guide for the mathcomp-analysis	library (WIP)

The purpose of this file is to document scripting techniques to be
used when contributing to mathcomp-analysis. It comes as an addition
to mathcomp's [contribution
guide](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md).

## `=>` vs. `-->` vs. `cvg` vs. `lim`

TODO: explain in particular the lemmas `cvgP`, `cvg_ex`

## `near` tactics vs. `filterS`, `filterS2`, `filterS3` lemmas

When dealing with limits, mathcomp-analysis favors filters
that are behind goals such as
```
{near \oo, G}.
```
In the presence of such goals, the `near` tactics can be used to
recover epsilon-delta reasoning
(see [this paper](https://doi.org/10.6092/issn.1972-5787/8124)).

However, when the proof does not require changing the epsilon it
is often worth using filters and lemmas such as
```
filterS : forall T (F : set (set T)), Filter F -> forall P Q : set T, P `<=` Q -> F P -> F Q
```
and its variants (`filterS2`, `filterS3`, etc.).

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

## TODO: Landau notations