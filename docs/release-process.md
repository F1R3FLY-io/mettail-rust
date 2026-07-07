# Release Process

This project uses **SemVer** driven by `workspace.package.version` in the root
`Cargo.toml`. Releases are cut on `main` by the `.github/workflows/release.yml`
workflow.

## Triggers

The release workflow runs on:

- **Nightly cron** at 06:00 UTC
- **Every push to `main`** (typically a dev → main PR merge)
- **Manual dispatch** via the Actions tab

Every run is gated: if a git tag `v<workspace version>` already exists, the
workflow exits without doing anything. Releases are cut only when the workspace
version has been bumped since the last tag.

## Contributor flow

All release prep happens on `dev`. `main` is protected and the release workflow
never writes to it.

1. Merge the work you want to ship into `dev`.
2. Bump `version` in `[workspace.package]` of the root `Cargo.toml`
   (e.g. `0.1.0` → `0.2.0`).
3. Run the changelog generator locally:

   ```sh
   ./AItools/scripts/generate-changelog.sh
   ```

   This reads the workspace version, collects commits since the last SemVer tag,
   and inserts a `## [X.Y.Z] - YYYY-MM-DD` section into `CHANGELOG.md`.
   Non-conventional commit messages are tolerated (they land under `### Changed`).

   Edit the generated entries if you want cleaner release notes — the workflow
   will use whatever is in `CHANGELOG.md` verbatim as the GitHub Release body.

4. Commit and open a PR from `dev` to `main`.
5. After merge, the release workflow will:
   - Tag `vX.Y.Z` on `main`
   - Create a GitHub Release using the `[X.Y.Z]` section of `CHANGELOG.md`
   - Publish any `publish`-enabled crates to crates.io (see below)

## crates.io publishing

By default, every workspace member has `publish = false` as a safety measure.
To make a crate publishable:

1. Remove `publish = false` from its `Cargo.toml`.
2. Ensure each intra-workspace path dependency also carries an explicit version:

   ```toml
   mettail-runtime = { path = "../runtime", version = "0.1.0" }
   ```

3. Confirm the crate has a `description`, `license`, and `repository` (most are
   inherited from `[workspace.package]`).

The publish job (`AItools/scripts/publish-crates.sh`) enumerates all publishable
members, topologically sorts them by workspace dependencies, and runs
`cargo publish -p <name>` for each. A 15-second sleep between publishes lets the
crates.io index catch up before dependents publish.

### Required repository secrets

| Secret                  | Used for                                      |
| ----------------------- | --------------------------------------------- |
| `GITHUB_TOKEN`          | Automatic (creates tag + GitHub Release)      |
| `CARGO_REGISTRY_TOKEN`  | `cargo publish` to crates.io                  |

## Branch protection assumptions

The workflow assumes `main` is protected:

- Direct pushes disabled
- PR required
- (Optional) passing CI required

The workflow never pushes commits to `main` — only annotated tags. If your
protection rules block tag pushes from the `github-actions[bot]`, configure
them to allow tag creation for that actor, or create a PAT and expose it as
a repository secret used by the tag-push step.

## Version-bump cadence

There is no automated bump. Bumping is an intentional act by a contributor
preparing a release PR. The nightly cron exists so that if a PR bumping the
version gets merged during off-hours, the release is still cut without waiting
for the next human push.
