# How to release

## Publish a release

1. Check that the milestone is complete.

2. Announce on Zulip:
- "We are preparing the X.Y.Z version of mathcomp-analysis,
  please do not merge into master until further notice."

3. Edit the changelogs
- Commit message: "changelog for version X.Y.Z"

4. Close the milestone.

5. Draft the release
   - [https://github.com/math-comp/analysis/releases](https://github.com/math-comp/analysis/releases)
   - Tag: `vX.Y.Z`
   - Title: "MathComp Analysis X.Y.Z"
   - Summary:
     + "Compatible with MathComp X.YZ, ..."
     + main change (extracted from the changelog?)
     + [changelog](https://github.com/math-comp/analysis/blob/master/CHANGELOG.md)

6. Announce to Zulip:
- "We have released the X.Y.Z version of mathcomp-analysis,
  it is now ok to merge into master."

## Publish the opam package

1. Update the date of the opam file in master

2. Submit a new opam package to [https://github.com/coq/opam-coq-archive](https://github.com/coq/opam-coq-archive)
- details omitted (for now?)

3. Annouce on Zulip:
- "The opam package the X.Y.Z version of mathcomp-analysis is available as an opam package in U."
  where U is among
  + https://coq.inria.fr/opam/released
  + https://coq.inria.fr/opam/extra-dev
