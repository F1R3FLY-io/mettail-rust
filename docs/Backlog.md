---
doc_type: backlog
version: "1.0"
last_updated: [DATE]
---

# Backlog

<!--
TEMPLATE USAGE INSTRUCTIONS:
0. Update the frontmatter date when modifying this file
   (Update version only for significant structural changes to template)
1. Replace all [PROJECT_NAME] and [PROJECT_SPECIFIC] markers
2. Add deferred or low-priority items here
3. Move items to docs/ToDos.md when ready to work on them
4. Remove these usage instruction comments before committing
-->

This document captures deferred work, future ideas, and low-priority items that aren't ready for active development.

**Document Structure**
- Active work: `docs/ToDos.md`
- User stories: `docs/UserStories.md`
- Completed work: `docs/CompletedTasks.md`
- Deferred work: This file (`docs/Backlog.md`)

**For LLM assistance in multi-repo workspace:**
See [Task Tracking Standard]([RELATIVE_PATH]/top-level-gitlab-profile/docs/common/task-tracking-standard.md)

**For reference (GitLab):**
[Task Tracking Standard](https://gitlab.com/smart-assets.io/gitlab-profile/-/blob/master/docs/common/task-tracking-standard.md)

---

## Backlog Categories

Items are organized by category and rough priority within each category.

---

### Technical Debt

Items that improve code quality, performance, or maintainability but aren't blocking active development.

---

#### BACKLOG-TD-001: [PROJECT_SPECIFIC: Item Title]

```yaml
---
backlog_id: BACKLOG-TD-001
title: "[PROJECT_SPECIFIC: Item Title]"
category: technical_debt
priority: p3
added_at: [DATE]
reason_deferred: "[PROJECT_SPECIFIC: Why this isn't active yet]"
promotion_criteria:
  - "[PROJECT_SPECIFIC: When should this become active?]"
---
```

**Description:** [PROJECT_SPECIFIC: What needs to be done?]

**Benefit:** [PROJECT_SPECIFIC: Why is this valuable?]

---

### Feature Ideas

Future features that have been identified but aren't yet prioritized.

---

#### BACKLOG-FI-001: [PROJECT_SPECIFIC: Feature Idea Title]

```yaml
---
backlog_id: BACKLOG-FI-001
title: "[PROJECT_SPECIFIC: Feature Idea Title]"
category: feature_idea
priority: p3
added_at: [DATE]
user_story: null         # Link when user story is created
reason_deferred: "[PROJECT_SPECIFIC: Why this isn't active yet]"
promotion_criteria:
  - "[PROJECT_SPECIFIC: When should this become active?]"
---
```

**Description:** [PROJECT_SPECIFIC: What is the feature?]

**Value Proposition:** [PROJECT_SPECIFIC: Who benefits and how?]

---

### Research & Exploration

Items that need investigation before they can become actionable tasks.

---

#### BACKLOG-RE-001: [PROJECT_SPECIFIC: Research Topic]

```yaml
---
backlog_id: BACKLOG-RE-001
title: "[PROJECT_SPECIFIC: Research Topic]"
category: research
priority: p3
added_at: [DATE]
questions:
  - "[PROJECT_SPECIFIC: Question to answer]"
  - "[PROJECT_SPECIFIC: Another question]"
---
```

**Context:** [PROJECT_SPECIFIC: Why is this research needed?]

**Expected Outcomes:** [PROJECT_SPECIFIC: What decisions will this inform?]

---

### Dependencies & Blockers

Items waiting on external factors (upstream releases, third-party APIs, etc.)

---

#### BACKLOG-DB-001: [PROJECT_SPECIFIC: Blocked Item]

```yaml
---
backlog_id: BACKLOG-DB-001
title: "[PROJECT_SPECIFIC: Blocked Item]"
category: blocked_external
priority: p2
added_at: [DATE]
blocked_by_external: "[PROJECT_SPECIFIC: What external factor?]"
expected_resolution: "[PROJECT_SPECIFIC: When might this unblock?]"
---
```

**Description:** [PROJECT_SPECIFIC: What is blocked?]

**When Unblocked:** [PROJECT_SPECIFIC: What should happen when this unblocks?]

---

## Backlog Template

Use this template when adding new backlog items:

```yaml
---
backlog_id: BACKLOG-XX-XXX
title: "Short descriptive title"
category: technical_debt | feature_idea | research | blocked_external
priority: p3
added_at: YYYY-MM-DD
reason_deferred: "Why this isn't active yet"
promotion_criteria:
  - "Condition that would make this active"
---
```

---

## Promoting Items to Active Work

When a backlog item is ready for active development:

1. Create an epoch in `docs/ToDos.md` based on the backlog item
2. Create or link a user story in `docs/UserStories.md` if needed
3. Remove the item from this backlog (or mark as `promoted: true`)
4. Add a note referencing the original backlog ID

---

## References

- **Active Work:** `docs/ToDos.md`
- **User Stories:** `docs/UserStories.md`
- **Completed Work:** `docs/CompletedTasks.md`
