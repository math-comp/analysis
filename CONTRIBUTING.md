# Contribution Guide for the mathcomp-analysis library (WIP)

The purpose of this file is to document coding styles to be
used when contributing to mathcomp-analysis. It comes as an addition
to mathcomp's [contribution
guide](https://github.com/math-comp/math-comp/blob/master/CONTRIBUTING.md).

## Policy for Pull Requests

Always submit a pull request for code and wait for the CI to pass before merging.
Text markup files may be edited directly though, should you have commit rights.

## `-->` vs. `cvg` vs. `lim`

- `F --> x` means `F` tends to `x`. _This is the preferred way of stating a convergence._ **Lemmas about it use the string `cvg`.**
- `lim F` is the limit of `F`, it makes sense only when `F` converges and defaults to a distinguished point otherwise.
  _It should only be used when there is no other expression for the limit._ **Lemmas about it use the string `lim`.**
- `cvg F` is defined as `F --> lim F`, and is equivalent through `cvgP` and `cvg_ex` to the existence of some `x` such that `F --> x`.
  _When the limit is known, `F --> x` should be preferred._ **Lemmas about it use the string `is_cvg`.**

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

The outcome is an expression with the normal Leibniz equality `=` and term `'o_F` which is not parsable.
See [this paper](https://doi.org/10.6092/issn.1972-5787/8124) for more explanation and
the header of the file [landau.v](https://github.com/math-comp/analysis/blob/master/theories/landau.v).

## Deprecation

Deprecations are introduced for breaking changes. For a simple renaming, the pattern is:
```
#[deprecated(since="analysis X.Y.Z", note="Use new_definition instead.")]
Notation old_definition := new_definition (only parsing).
```
Note that this needs to be at the top-level (i.e., not inside a section).

When a lemma `lem` is scheduled for deletion, it ought better be renamed `__deprecated__lem`
(so that it can be blacklisted). The deprecation command then becomes:
```
#[deprecated(since="analysis X.Y.Z", note="Use another_lemma instead.")]
Notation lem := __deprecated__lem (only parsing).
```
The `(only parsing)` format is needed so that Coq does not print back the deprecated name
(for example when displaying error messages, that would be confusing).

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

### Properties of functions

- when a lemma is about a composite, we use the single letter suffix (when it exists)
  + e.g., `cvgM`, `continuousM`, `deriveX`, or `measurable_funX`
- when a lemma is about applied functions, we use the multi-letter prefix instead
  + e.g., `mul_continuous`, `exp_derive`, or `exp_measurable_fun`
