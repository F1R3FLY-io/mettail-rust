<!--
ROADMAP TEMPLATE

Usage:
1. Copy this template to your project's docs/ directory as docs/roadmap.md
   (or to the repo root as ROADMAP.md if docs/ is not used).
2. Replace all <PLACEHOLDER> markers with actual content.
3. Keep the frontmatter schema intact; consuming tooling depends on it.
4. Update `updated:` whenever the file is edited.
5. Remove these usage instruction comments before committing.

This template is governed by:
  docs/common/roadmap-release-normalization-standard.md

Required behavior:
- Nearest-term releases MUST carry a calendar `target_date` (YYYY-MM-DD).
- Long-horizon entries MAY use the `YYYY-QN` quarter form.
- Versions MUST follow strict SemVer: vMAJOR.MINOR.PATCH[-pre-release].
-->
---
doc_type: roadmap
repo: <repo-name>
updated: YYYY-MM-DD
horizon_months: 6
owners:
  - github: <maintainer-username>
    email: <optional@address>
releases:
  - version: vX.Y.Z
    target_date: YYYY-MM-DD
    milestone: "vX.Y.Z — <theme>"
    status: planned
    theme: <one-line description>
    notes: <optional context>
  - version: vX.Y+1.0
    target_date: YYYY-QN
    milestone: "vX.Y+1.0 — <theme>"
    status: planned
    theme: <one-line description>
---

# <Repo Name> Roadmap

> This file is governed by the [Roadmap, Release Date, and Version Normalization Standard](../common/roadmap-release-normalization-standard.md).
> Update the `updated:` frontmatter field whenever this file is edited.
> Nearest-term releases MUST carry a calendar `target_date`; long-horizon entries MAY use the `YYYY-QN` quarter form.

## Current Focus

<Short paragraph describing what is actively being worked on and how it maps to the nearest release.>

## Upcoming Releases

### vX.Y.Z — <theme>

- **Target:** YYYY-MM-DD
- **Milestone:** [vX.Y.Z — <theme>](<milestone-url>)
- **Status:** planned | in_progress

<Scope summary: what is in, what is out, and known risks.>

### vX.Y+1.0 — <theme>

- **Target:** YYYY-QN
- **Milestone:** _to be created_
- **Status:** planned

<Scope summary.>

## Out of Scope / Deferred

- <Item> — <reason for deferral>

## Change Log

| Date | Change |
|------|--------|
| YYYY-MM-DD | Initial roadmap created from roadmap.md.template |
