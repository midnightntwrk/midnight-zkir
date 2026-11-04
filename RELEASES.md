# Releasing ZKIR

ZKIR releases use two manually triggered GitHub Actions workflows:

| Step        | Workflow                                                                 | What it does                                                                                                                                       |
| ----------- | ------------------------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------------------------- |
| Pre-release | **Prepare ZKIR Release** (`.github/workflows/prepare-release.yml`)       | Bumps versions, refreshes `Cargo.lock`, promotes `CHANGELOG.md`, scaffolds release notes, and opens a release PR.                                  |
| Release     | **Publish ZKIR Release** (`.github/workflows/release.yml`)               | Builds and tests the release, pushes the `zkir-<version>` tag, publishes to npm and crates.io, and creates the GitHub Release.                      |

Both workflows act on the head of the branch they are dispatched from:

- **Prepare ZKIR Release** is dispatched from the **target branch**: the
  branch the release is cut from and merged back into. Usually this is the
  **base branch**: the repository's default branch, which tracks the current
  major release (currently `zkir-v3`). See
  [Releasing only some of the changes on the base branch](#releasing-only-some-of-the-changes-on-the-base-branch)
  for when it is not.
- **Publish ZKIR Release** is dispatched from the **release PR branch**
  (`release/zkir-<version>`) that the prepare workflow creates. This branch
  contains only the approved release, so anything merged into the target
  branch in the meantime can't end up in the release.

## Before you start

- Make sure the target branch is green in CI.
- Make sure the `## Unreleased` section of `CHANGELOG.md` lists everything
  that ships in this release. The prepare workflow turns this section into the
  release's changelog entry.
- Choose the version numbers:
  - `version`: the `zkir` crate version. It sets the git tag
    (`zkir-<version>`), for example `3.1.0` or `3.1.0-rc.1`.
  - `wasm_version` (optional): the `zkir-wasm` and npm package version. If you
    leave it empty, it uses `version`.
  - Versions with `-rc`, `-alpha`, or `-beta` are pre-releases. They don't get
    curated release notes, they are published to npm under a matching
    dist-tag, they are marked as pre-releases on GitHub, and they skip
    crates.io.

## 1. Run the pre-release CI job

1. Go to **Actions → Prepare ZKIR Release → Run workflow**.
2. Under **Use workflow from**, select the target branch.
3. Enter `version` (and `wasm_version` if it should differ), then run the
   workflow.

The workflow pushes a `release/zkir-<version>` branch with a
`chore: prepare zkir-<version>` commit and opens a **Prepare
zkir-<version>** PR into the target branch.

## 2. Get approval

Review and finish the release PR. Its checklist covers:

- [ ] Versions are correct in the `Cargo.toml`, `zkir-wasm/package.json`, and
      `Cargo.lock` diffs.
- [ ] The `CHANGELOG.md` entry has been reviewed and edited.
- [ ] Final releases only: the prose in
      `.github/release-notes/zkir-<version>.md` has been written, and the draft
      bullets and placeholder comments have been removed.

Push any edits directly to the `release/zkir-<version>` branch. The PR needs
the usual CI checks and an approving review from the code owners (see
`CODEOWNERS`).

Only push release-prep edits to the release PR branch. Don't merge or rebase
the target branch into it: whatever is on this branch is exactly what gets
released.

## 3. Cut the release with the release CI job

Once the PR is approved and green, but **before merging it**, run the release
job against the release PR branch:

1. Optional but recommended: go to **Actions → Publish ZKIR Release → Run
   workflow**, set **Use workflow from** to `release/zkir-<version>`, and tick
   **dry_run**. This builds, tests, and assembles the artifacts without pushing
   a tag or publishing anything. You can inspect the result in the
   `release-assets` artifact.
2. Run **Publish ZKIR Release** from `release/zkir-<version>` again with
   **dry_run** unticked.
3. The run waits for a reviewer to approve it on the protected `release`
   environment. When it is approved, it:
   - pushes the `zkir-<version>` tag on the head of `release/zkir-<version>`,
   - re-runs the unit tests,
   - publishes `zkir-v3` to GitHub Packages and npmjs under both
     `@midnight-ntwrk` and `@midnightntwrk`,
   - publishes `midnight-zkir` to crates.io (final releases only),
   - creates the GitHub Release with the npm tarball, test results, and
     `SHA256SUMS`.
4. Check that the GitHub Release, npm packages, and crates.io crate are all
   there.

The workflow can safely be re-run. It skips an existing tag, skips npm versions
that are already published (unless **force** is ticked), and refreshes the
assets of an existing GitHub Release.

> **Note:** If the `release` environment restricts which branches can deploy
> (**Settings → Environments → release → Deployment branches**), it must allow
> `release/*`.

## 4. Merge back into the target branch

After the release is published, merge the release PR into the target branch.

- Use a **merge commit**, not squash or rebase. That way the tagged commit is
  part of the target branch's history. Squashing or rebasing would leave the
  `zkir-<version>` tag on a commit that is not on the target branch.
- If the target branch has moved on since the release PR was opened, resolve
  conflicts on the PR branch by merging the target branch into it. This
  creates a commit after the tagged one, so it doesn't change what was
  released.
- The `release/zkir-<version>` branch can be deleted after merging. The tag
  keeps the released commit.

## Releasing only some of the changes on the base branch

Sometimes the base branch contains work that isn't ready to ship. To release
only part of it, cut the release from a dedicated branch instead of the base
branch:

1. **Branch off a specific commit.** Pick the last commit on the base branch
   that should be in the release, and push a release branch from it:

   ```sh
   git fetch origin
   git switch -c release-3.1 <commit-sha>
   git push -u origin release-3.1
   ```

   If you need a fix that landed after that commit, cherry-pick it onto the
   release branch through a normal PR.

2. **Edit the changelog.** On the release branch, make sure the `## Unreleased`
   section of `CHANGELOG.md` lists only the changes this branch actually
   contains. Merge this edit before preparing the release.

3. **Run the pre-release CI job on that branch.** Dispatch **Prepare ZKIR
   Release** with **Use workflow from** set to `release-3.1`. The release PR
   goes from `release/zkir-<version>` into `release-3.1`, not the base branch.

4. **Get approval.** Follow [step 2](#2-get-approval).

5. **Release from the release PR branch.** Follow
   [step 3](#3-cut-the-release-with-the-release-ci-job): dispatch **Publish
   ZKIR Release** from `release/zkir-<version>`.

6. **Merge back into the release branch.** Follow
   [step 4](#4-merge-back-into-the-target-branch) with `release-3.1` as the
   target branch.

7. **Merge back into the base branch.** Open a PR from `release-3.1` into the
   base branch and merge it with a merge commit, so that the base branch gets
   the version bumps, the new changelog section, the release notes, and any
   cherry-picked fixes. When you resolve conflicts:
   - Keep the version numbers from the release.
   - In `CHANGELOG.md`, put the new `## ZKIR <version>` section below
     `## Unreleased`. Keep any base-branch-only entries (the changes that were not
     released) under `## Unreleased`, and remove entries that are now in the
     released section.

Keep the release branch for later patch releases (for example `3.1.1`) of the
same line. Repeat steps 3–7 for each one.
