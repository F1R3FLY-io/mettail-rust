---
doc_type: completed_tasks
version: "1.0"
last_updated: [DATE]
---

# Completed Tasks

<!--
TEMPLATE USAGE INSTRUCTIONS:
0. Update the frontmatter date when modifying this file
   (Update version only for significant structural changes to template)
1. Replace all [PROJECT_NAME] and [PROJECT_SPECIFIC] markers
2. Move completed epochs here from docs/ToDos.md
3. Maintain chronological order (newest at top)
4. Remove these usage instruction comments before committing
-->

This document archives completed epochs and tasks for historical reference and progress tracking.

**Document Structure**
- Active work: `docs/ToDos.md`
- User stories: `docs/UserStories.md`
- Completed work: This file (`docs/CompletedTasks.md`)
- Deferred work: `docs/Backlog.md`

**For LLM assistance in multi-repo workspace:**
See [Task Tracking Standard]([RELATIVE_PATH]/top-level-gitlab-profile/docs/common/task-tracking-standard.md)

**For reference (GitLab):**
[Task Tracking Standard](https://gitlab.com/smart-assets.io/gitlab-profile/-/blob/master/docs/common/task-tracking-standard.md)

---

## Completed Epochs

<!-- Epochs are listed in reverse chronological order (newest first) -->

---

### EPOCH-XXX: [PROJECT_SPECIFIC: Epoch Title]

```yaml
---
epoch_id: EPOCH-XXX
title: "[PROJECT_SPECIFIC: Epoch Title]"
status: complete
priority: p1
user_story: US-XXX
completed_at: [DATE]
completed_by: [SESSION_ID or contributor]
mr_pr: "[PROJECT_SPECIFIC: MR/PR link if applicable]"
tasks:
  - id: TASK-XXX-1
    title: "[PROJECT_SPECIFIC: Task 1 title]"
    status: complete
    completed_at: [DATE]

  - id: TASK-XXX-2
    title: "[PROJECT_SPECIFIC: Task 2 title]"
    status: complete
    completed_at: [DATE]
---
```

**Summary:** [PROJECT_SPECIFIC: Brief summary of what was accomplished]

**Key Changes:**
- [PROJECT_SPECIFIC: Change 1]
- [PROJECT_SPECIFIC: Change 2]

**Lessons Learned:**
- [PROJECT_SPECIFIC: What went well or what to do differently]

---

<!-- Add more completed epochs following the same format -->

---

## Completion Statistics

<!-- Optional: Track metrics over time -->

| Period | Epochs Completed | Tasks Completed | Notes |
|--------|------------------|-----------------|-------|
| [PROJECT_SPECIFIC: Period] | [Count] | [Count] | [Notes] |

---

## Archive Format

When moving epochs from `docs/ToDos.md` to this file:

1. Copy the entire epoch block (YAML frontmatter + context)
2. Update `status: complete`
3. Add `completed_at`, `completed_by`, and optionally `mr_pr`
4. Update all task statuses to `complete` with `completed_at` dates
5. Add a brief **Summary** section
6. Optionally add **Key Changes** and **Lessons Learned**

---

## References

- **Active Work:** `docs/ToDos.md`
- **User Stories:** `docs/UserStories.md`
- **Backlog:** `docs/Backlog.md`
