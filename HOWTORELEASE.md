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
   - [github.com/math-comp/analysis/releases/new](https://github.com/math-comp/analysis/releases/new?tag=X.Y.Z%20%28no%20v%20prefix%29&title=MathComp%20Analysis%20X.Y.Z&body=Compatible%20with%20MathComp%20X.Y.Z%2C%20...%0AThe%20main%20changes%20are%20...%0ASee%20the%20%5Bchangelog%5D%28https%3A%2F%2Fgithub.com%2Fmath-comp%2Fanalysis%2Fblob%2Fmaster%2FCHANGELOG.md%29)
   - Tag: `X.Y.Z` (no `v` prefix)
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
