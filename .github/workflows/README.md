# GitHub Actions Workflows

This directory contains workflows that automate testing, building, releasing,
and publishing for the Verus project.

## Workflows Overview

### 1. CI Workflow (`ci.yml`)

**Triggers:**
- Push to `main` branch
- Pull requests (opened, synchronized, reopened)
- Manual dispatch

**Purpose:** Comprehensive testing and continuous binary distribution

**Jobs:**

1. **`fmt`** (linux)
   - Validates Rust code formatting with `rustfmt`
   - Validates `vstd` formatting with `verusfmt`

2. **`full-test`** (macOS ARM64)
   - Runs full test suite.

3. **`basic-test`** (macOs x64, Windows x64, and Linux x64)
   - Runs basic tests only

3. **`smoke-test`** (macOs ARM64)
   - Checks that `verus` builds with esoteric configurations
   - Runs minimal tests relevant to the configuration

4. **`build-docs`** (linux)
   - Builds the `verusdoc` artifact
   - Uploads `verusdoc` artifact for documentation deployment

5. **`build-release`** (macOS ARM64, macOs x64, Windows x64, and Linux x64)
   - Builds release binary artifacts for every supported platform
   - Uploads `verus-<arch>-<os>.zip` artifacts

6. **`release`** (linux)
   - **Only runs on push to `main`** (not PRs)
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
- Documentation artifacts for GitHub Pages deployment
- Platform artifacts available for download from the workflow run

---

### 2. Release Workflow (`release.yml`)

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

**Relationship to CI Workflow:**

```
┌─────────────────────────────────────────────────────────────┐
│                      CI Workflow (ci.yml)                   │
│                                                             │
│  1. Push to main → Build & Test → Create artifacts          │
│  2. Update Rolling Release (ID: 163437062)                  │
│     - Tag: release/rolling/v0.23.1                          │
│     - Name: "Rolling Release v0.23.1"                       │
│     - Assets: verus-<version>-<platform>.zip (4 platforms)  │
│     - Always points to latest successful main build         │
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

### 3. Pages Workflow (`pages.yml`)

**Triggers:**
- Workflow run completion (after `ci.yml` completes successfully on `main`)

**Purpose:** Build and deploy project documentation to GitHub Pages

**Jobs:**

1. **`build`** (Linux)
   - Sets up mdbook for building documentation
   - Builds user guide: `source/docs/guide` → `/_site/guide`
   - Builds state machines guide: `source/docs/state_machines` → `/_site/state_machines`
   - Downloads `verusdoc` artifact from CI workflow
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

### 4. Crate Updates Workflow (`crate-updates.yml`)

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
main branch push → ci.yml (builds & tests)
                    │
                    ├─→ Creates/updates Rolling Release
                    │
                    └─→ pages.yml (on success) → GitHub Pages deployment

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
