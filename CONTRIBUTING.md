# Contribution Guide for the mathcomp-analysis	library (WIP)

The purpose of this file is to document coding styles to be
used when contributing to mathcomp-analysis. It comes as an addition
to mathcomp's [contribution
guide](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md).

## Policy for Pull Requests

Always submit a pull request for code and wait for the CI to pass before merging.
Text markup files may be edited directly though, should you have commit rights.

## `-->` vs. `cvg` vs. `lim`

- `F --> x` means `F` tends to `x`. _This is the preferred way of stating a convergence._ **Lemmas about it use the string `cvg`.**
- `lim F` is the limit of `F`, it makes sense only when `F` converges and defaults to a distinguished point otherwise. _It should only be used when there is no other expression for the limit._ **Lemmas about it use the string `lim`.**
- `cvg F` is defined as `F --> lim F`, and is equivalent through `cvgP` and `cvg_ex` to the existence of some `x` such that `F --> x`. _When the limit is known, `F --> x` should be preferred._ **Lemmas about it use the string `is_cvg`.**

## `near` tactics vs. `filterS`, `filterS2`, `filterS3` lemmas

When dealing with limits, mathcomp-analysis favors filters
phrasing, as in
```
\forall x \near \oo, P x.
```
In the presence of such goals, the `near` tactics can be used to
recover epsilon-delta reasoning
(see [this paper](https://doi.org/10.6092/issn.1972-5787/8124)).

However, when the proof does not require changing the epsilon it
is might be worth using filter combinators, i.e. lemmas such as
```
filterS : forall T (F : set (set T)), Filter F -> forall P Q : set T, P `<=` Q -> F P -> F Q
```
and its variants (`filterS2`, `filterS3`, etc.).

## Landau notations

Landau notations can be written in four shapes:
- `f =o_F e` (i.e. functional with a simple right member, thus a binary notation)
- `f = g +o_F e` (i.e. functional with an additive right member, thus ternary)
- `f x =o_(x \near F) (e x)` (i.e. pointwise with a simple right member, thus binary)
- `f x = g x +o_(x \near F) (e x)` (i.e. pointwise with an additive right member, thus ternary)

The outcome is an expression with the normal Leibniz equality `=` and term `'o_F` which is not parsable. See [this paper](https://doi.org/10.6092/issn.1972-5787/8124) for more explanation and the header of the file [landau.v](https://github.com/math-comp/analysis/blob/master/theories/landau.v).

## Naming convention

### homo and mono notations

Statements of `{homo ...}` or `{mono ...}` shouldn't be named after `homo`, or `mono`
(just as for `{morph ...}` lemmas). Instead use the head of the unfolded statement
(for `homo`) or the head of the LHS of the equality (for `mono`), as in
```coq
Lemma le_contract : {mono contract : x y / (x <= y)%O}.
```

When a `{mono ...}` lemma subsumes `{homo ...}`, it gets priority
for the short name, and, if really needed, the corresponding `{homo ...}`
lemma can be suffixed with `W`. If the `{mono ...}` lemma is
only valid on a subdomain, then the `{homo ...}` lemma takes the
short name, and the `{mono ...}` lemma gets the suffix `in`.

### Suffixes for names of lemmas

- The construction `_ !=set0` corresponds to suffix `nonempty`
- The construction `_ != set0` corresponds to suffix `neq0`

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
