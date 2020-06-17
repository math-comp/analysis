# Contribution Guide for the mathcomp-analysis	library (WIP)

The purpose of this file is to document scripting techniques to be
used when contributing to mathcomp-analysis. It comes as an addition
to mathcomp's [contribution
guide](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md).

## Policy for Pull Requests

Always submit a pull request for code and wait for the CI to pass before merging.
Text markup files may be edited directly though, should you have commit rights.

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

## Landau notations

TODO

## Naming convention

### homo and mono notations

Statements of `{homo ...}` or `{mono ...}` shouldn't be named after `homo`, or `mono`
(just as for `{morph ...}` lemmas). Instead use the head of the unfolded statement
(for `homo`) or the head of the LHS of the equality (for `mono`).

When a `{mono ...}` lemma subsumes `{homo ...}`, it gets priority
for the short name, and, if really needed, the corresponding `{homo ...}`
lemma can be suffixed with `W`. If the `{mono ...}` lemma is
only valid on a subdomain, then the `{homo ...}` lemma takes the
short name, and the `{mono ...}` lemma gets the suffix `in`.

## Idioms

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
