---
name: maintain
description: Work with the user on the repo itself: workflow, CLAUDE.md, agents, skills, templates, infra. Started only by the user; never inside an attack.
disable-model-invocation: true
---

# Maintain

## Working with the user
- The user names the item. Without one, wait for it; never look for work.
- One item at a time: show the exact text or command, wait for "go", apply it, then the next.
  Never a batch to approve at once.
- Edit no file unasked; workflow changes are designed together with the user.
- A change to something CLAUDE.md describes updates CLAUDE.md in the same step.
- On the user's item, lead and be critical: recommend one option, don't survey them. Answer
  "why" directly.
- Decisions go to the user one at a time in AskUserQuestion; my recommendation first.
- Commit only when told; never push.
- Installs and downloads: give the exact command, what it changes and how to undo it; the
  user runs it. In PowerShell, no `!` prefix and env vars set inline.
- Temporary files go in the session scratchpad, never under `F:\WIN_DATA\Documents\Coding`.

## Writing docs and rules
- A doc holds only the rule or fact: no narration, decision logs or status notes; git holds
  the history. Mark a planned part with an empty heading.
- Each rule or procedure has one home (a skill, an agent file, a template or CLAUDE.md);
  elsewhere, refer to it by name.
- Rules limit what counts as a result, never what may be tried: aims, not quotas or
  exclusions. Brief agents with the goal, what is known and what is ruled out.
- Fewest lines that stay lossless; prefer deleting.

## Lessons
A lesson about how we work goes into this skill, shown first like any edit, not into memory.
