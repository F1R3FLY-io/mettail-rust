---
doc_type: todos
version: "1.0"
last_updated: [DATE]
mr_status:
  ready: false
  target_branch: main
---

# Tasks and Epochs

<!--
TEMPLATE USAGE INSTRUCTIONS:
0. Update the frontmatter date when modifying this file
   (Update version only for significant structural changes to template)
1. Replace all [PROJECT_NAME] and [PROJECT_SPECIFIC] markers
2. Add new epochs using the YAML frontmatter format below
3. Move completed epochs to docs/CompletedTasks.md
4. Use /nextTask to find the next task to work on
5. Use /implement to execute tasks with full context
6. Remove these usage instruction comments before committing
-->

This document tracks implementation work through **epochs** (logical groupings of related tasks).

**Document Structure**
- Active work: This file (`docs/ToDos.md`)
- User stories: `docs/UserStories.md`
- Completed work: `docs/CompletedTasks.md`
- Backlog: `docs/Backlog.md`

**For LLM assistance in multi-repo workspace:**
See [Task Tracking Standard]([RELATIVE_PATH]/top-level-gitlab-profile/docs/common/task-tracking-standard.md)

**For reference (GitLab):**
[Task Tracking Standard](https://gitlab.com/smart-assets.io/gitlab-profile/-/blob/master/docs/common/task-tracking-standard.md)

---

## MR/PR Tracking

When all tasks in this file are complete and ready for merge, update the frontmatter:

```yaml
mr_status:
  ready: true
  target_branch: main
  title: "feat: [PROJECT_SPECIFIC: MR title]"
  description: |
    ## Summary
    - [Completed items]

    ## Test plan
    - [x] All tests passing
  labels: ["feature", "enhancement"]
```

---

## Active Epochs

<!-- Epochs are ordered by priority. Work on the highest priority epoch first. -->

---

### EPOCH-001: [PROJECT_SPECIFIC: Epoch Title]

```yaml
---
epoch_id: EPOCH-001
title: "[PROJECT_SPECIFIC: Epoch Title]"
status: pending          # pending | in_progress | blocked | review | complete
priority: p1             # p0 (critical) | p1 (high) | p2 (medium) | p3 (low)
user_story: US-XXX       # Link to user story in docs/UserStories.md
blocked_by: []           # List of blocking epoch IDs
created_at: [DATE]
claimed_by: null         # Implementer ID: human-{email}, {tool}-session[-{id}], or {team}/{role}
claimed_at: null
tasks:
  - id: TASK-001-1
    title: "[PROJECT_SPECIFIC: Task 1 title]"
    status: pending      # pending | in_progress | complete | blocked
    acceptance:
      - "[PROJECT_SPECIFIC: Acceptance criterion 1]"
      - "[PROJECT_SPECIFIC: Acceptance criterion 2]"

  - id: TASK-001-2
    title: "[PROJECT_SPECIFIC: Task 2 title]"
    status: pending
    blocked_by: [TASK-001-1]  # Optional: task dependencies
    acceptance:
      - "[PROJECT_SPECIFIC: Acceptance criterion 1]"
---
```

**Context:** [PROJECT_SPECIFIC: Why is this epoch needed? What problem does it solve?]

**Scope:**
- [PROJECT_SPECIFIC: What's included]
- [PROJECT_SPECIFIC: What's explicitly excluded]

**Notes:**
- [PROJECT_SPECIFIC: Implementation notes, gotchas, references]

---

<!-- Add more epochs following the same format -->

---

## Epoch Template

Use this template when adding new epochs:

```yaml
---
epoch_id: EPOCH-XXX
title: "Short descriptive title"
status: pending
priority: p2
user_story: US-XXX
blocked_by: []
created_at: YYYY-MM-DD
claimed_by: null         # Implementer ID: human-{email}, {tool}-session[-{id}], or {team}/{role}
claimed_at: null
tasks:
  - id: TASK-XXX-1
    title: "Task description"
    status: pending
    acceptance:
      - "Measurable acceptance criterion"
---
```

---

## Task States

| Status | Meaning | Next Action |
|--------|---------|-------------|
| `pending` | Not started | Available to claim |
| `in_progress` | Being worked on | Continue or handoff |
| `blocked` | Waiting on dependency | Check `blocked_by` |
| `review` | Ready for review | Review and approve |
| `complete` | Done | Move to CompletedTasks.md |

---

## Workflow

1. **Find next task**: Use `/nextTask` to identify the highest priority unclaimed task
2. **Claim task**: Set `claimed_by` using [Implementer Identification](../common/stigmergic-collaboration.md#implementer-identification) format and `status: in_progress`
3. **Implement**: Use `/implement` to execute with full context
4. **Complete**: Mark `status: complete` when acceptance criteria met
5. **Move epoch**: When all tasks complete, move epoch to `docs/CompletedTasks.md`

---

## References

- **User Stories:** `docs/UserStories.md`
- **Completed Work:** `docs/CompletedTasks.md`
- **Backlog:** `docs/Backlog.md`
- **MR/PR Tracking Standard:** [docs/common/todos-mr_pr-tracking-standard.md]([RELATIVE_PATH]/top-level-gitlab-profile/docs/common/todos-mr_pr-tracking-standard.md)
