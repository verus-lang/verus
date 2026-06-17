# GitHub Actions Workflows

This directory contains workflows that automate testing, building, releasing,
and publishing for the Verus project.

## Workflows Overview

### 1. CI Workflow (`ci.yml`)

**Triggers:**

- Pull requests (opened, synchronized, reopened)
- Merge queue (`merge_group`)
- Manual dispatch

**Purpose:** Comprehensive testing that gates a PR's merge.

**Jobs:**

1. **`fmt`** (linux)
   - Validates Rust code formatting with `rustfmt`
   - Validates `vstd` formatting with `verusfmt`

2. **`change_filter`** (linux)
   - Detects whether `source/cargo-verus/**` changed

3. **`cargo-verus-test`** (linux)
   - Only runs on changes to `source/cargo-verus/**`
   - Runs `cargo-verus` tests (unit- and package-level)
   - Runs after `fmt` and `clippy` pass

4. **`full-test`** (macOS ARM64)
   - Runs full test suite.

5. **`basic-test`** (macOs x64, Windows x64, and Linux x64)
   - Runs basic tests only

6. **`smoke-test`** (macOs ARM64)
   - Checks that `verus` builds with esoteric configurations
   - Runs minimal tests relevant to the configuration

7. **`build-docs`** (linux)
   - Builds the `verusdoc` artifact with `--strict` (treats warnings as
     errors) as a pre-merge validation check
   - Does **not** upload the artifact; `pages.yml` builds its own copy
     for deployment

**Output:**

- A green merge-queue check that gates the PR's merge to `main`
- Post-merge artifact production lives in `rolling-release.yml` and
  `pages.yml`

---

### 2. Rolling Release Workflow (`rolling-release.yml`)

**Triggers:**

- Push to `main` (every commit landing via the merge queue)
- Manual dispatch

**Purpose:** Continuously update the rolling pre-release with binaries
built from the latest `main`. Trusts the merge queue to have verified
the commit via `ci.yml`.

**Jobs:**

1. **`build`** (macOS ARM64, macOS x64, Windows x64, Linux x64)
   - Builds release binary artifacts for every supported platform
   - Uploads `verus-<arch>-<os>.zip` artifacts

2. **`publish`** (linux)
   - Downloads all platform artifacts
   - Extracts version information from `version.txt`
   - Updates the existing **Rolling Release** (GitHub release ID: 163437062)
   - Tags release as `release/rolling/<version>`
   - Names release as `Rolling Release <version>`
   - Uploads all platform binaries to the rolling release
   - Deletes old rolling release tags and assets
   - Publishes the updated rolling release

**Output:**

- Continuous binary distribution via the Rolling Release

---

### 3. Release Workflow (`release.yml`)

**Triggers:**

- Schedule: Weekly on Mondays at midnight UTC

**Purpose:** Promote a Rolling Release to a permanent versioned release

**How it works:**

1. **Fetches Rolling Release Data**
   - Queries GitHub API for the rolling release (ID: 163437062)
   - Extracts tag name (e.g., `release/rolling/v0.23.1`)
   - Extracts release name (e.g., `Rolling Release v0.23.1`)
   - Gets list of attached assets

2. **Creates New Permanent Release**
   - Strips `/rolling` from tag: `release/rolling/v0.23.1` → `release/v0.23.1`
   - Strips `Rolling ` from name: `Rolling Release v0.23.1` → `Release v0.23.1`
   - Creates new GitHub release with the permanent tag/name
   - Tags the commit that was used for the rolling release

3. **Copies Assets**
   - Downloads each asset from the rolling release
   - Re-uploads to the new permanent release
   - Preserves asset names and contents

**Relationship to Rolling Release Workflow:**

```
┌─────────────────────────────────────────────────────────────┐
│             Rolling Release Workflow                        │
│             (rolling-release.yml)                           │
│                                                             │
│  1. Push to main → Build → Create artifacts                 │
│  2. Update Rolling Release (ID: 163437062)                  │
│     - Tag: release/rolling/v0.23.1                          │
│     - Name: "Rolling Release v0.23.1"                       │
│     - Assets: verus-<version>-<platform>.zip (4 platforms)  │
│     - Always points to latest main build                    │
│                                                             │
└─────────────────┬───────────────────────────────────────────┘
                  │
                  │ Rolling release is continuously updated
                  │ with every push to main
                  │
                  ▼
┌─────────────────────────────────────────────────────────────┐
│                  Release Workflow (release.yml)             │
│                                                             │
│  1. Scheduled weekly release to publish a new version       │
│  2. Copies current rolling release to permanent release     │
│     - Tag: release/v0.23.1 (strips "/rolling")              │
│     - Name: "Release v0.23.1" (strips "Rolling ")           │
│     - Assets: Same binaries from rolling release            │
│     - Permanent snapshot, never updated                     │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**Key Distinction:**

- **Rolling Release**: Ephemeral, continuously updated with latest main
- **Permanent Release**: Immutable snapshot at a point in time
- Users tracking development use the rolling release
- Users wanting stable versions use permanent releases

---

### 4. Pages Workflow (`pages.yml`)

**Triggers:**

- Push to `main` (every commit landing via the merge queue)
- Manual dispatch

**Purpose:** Build and deploy project documentation to GitHub Pages

**Jobs:**

1. **`build`** (Linux)
   - Builds the `verusdoc` artifact via `./tools/docs.sh`
   - Sets up mdbook for building documentation
   - Builds user guide: `source/docs/guide` → `/_site/guide`
   - Builds state machines guide: `source/docs/state_machines` → `/_site/state_machines`
   - Copies verusdoc into the site at `/_site/verusdoc`
   - Builds publications/projects page using Jekyll
   - Builds Verus landing page using Jekyll
   - Uploads combined site artifact

2. **`deploy`** (Linux)
   - Deploys the built site to GitHub Pages
   - Makes documentation available at the GitHub Pages URL

**Output:**

- User-facing documentation at the project's GitHub Pages site
- API documentation (verusdoc)
- Tutorial guides
- Publications and projects listings

---

### 5. Crate Updates Workflow (`crate-updates.yml`)

**Triggers:**

- Manual dispatch
- Schedule: Weekly on Sundays at midnight UTC
  - This way, the updated versions are incorporated into the Monday release

**Purpose:** Automated maintenance of published crates on crates.io

**Assumptions:**

1. Assumes that `main` is in a building and verifying state.

**Jobs:**

1. **`bump-crate-versions`** (linux)
   - Runs version bump tool: `source/tools/bump_crate_versions` with update command
   - Commits version changes if needed
   - Pushes changes to `main`
   - Publishes updated crates to crates.io

---

## Workflow Dependencies

```
PR / merge queue → ci.yml (gates merge to main)

main branch push → rolling-release.yml → Updates Rolling Release
                 → pages.yml            → GitHub Pages deployment

release.yml (weekly/manual) → Copies Rolling Release → Permanent Release

crate-updates.yml (weekly/manual) → Updates crate versions → Publishes to crates.io
```

## Required Secrets

- `GITHUB_TOKEN` - Automatically provided by GitHub Actions (for releases and pages)
- `CARGO_REGISTRY_TOKEN` - Required for `crate-updates.yml` to publish to crates.io

## Platform Support

All workflows build and test Verus on:

- **Linux**: `x86_64` (ubuntu-22.04)
- **macOS**: ARM64 (macOS 14) and `x86_64` (macOS 15)
- **Windows**: `x86_64` (2022)

ARM64 macOS receives full testing; other platforms run smoke tests for efficiency.

The general rule of thumb is that we lag one version behind the latest offered on Github.

_Note_: when updating the OS versions used here, be sure to update the versions listed in the Support section of [INSTALL.md](../../INSTALL.md).
