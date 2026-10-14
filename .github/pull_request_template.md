##### Motivation for this change

<!-- if this PR fixes an issue, use "fixes #XYZ" -->

<!-- briefly explain what the PR provides (and what it does not do if applicable, e.g., incomplete fixes), mention related issues, PRs, Zulip conversations, papers, etc. so that readers (including reviewers) have maximum context -->

##### Checklist

- [ ] appended entries in the relevant sections of `CHANGELOG_UNRELEASED.md`

<!-- append contents at the end of each relevant sections to minimize conflicts and ease rebasing/merging -->
<!-- consider using a temporary CHANGELOG_PR1234.md instead to avoid conclict while working on the PR -->
<!-- consider the use of `changelog/changes.sh` from
     https://github.com/math-comp/tools to generate the changelog -->

- [ ] added corresponding documentation in the headers

Reference: [How to document](https://github.com/math-comp/math-comp/wiki/How-to-document)

<!-- Cross-out the above items using ~crossed out item~ when irrelevant -->

##### Merge policy

As a rule of thumb:
- PRs with several commits that make sense individually and that
  all compile are likely to be merged as they are into master.
- PRs with disorganized commits are very likely to be squash-rebased.

##### Reminder to reviewers

- Read [this Checklist](https://github.com/math-comp/math-comp/wiki/Checklist-for-creating-and-review-PRs)
- Put a milestone if possible
- Check labels
