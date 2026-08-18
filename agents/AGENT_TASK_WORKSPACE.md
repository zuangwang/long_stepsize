# Agent Task Workspace

This directory preserves the Codex instruction relay inside the source
repository. It keeps task coordination separate from source code, results,
and other project files.

## Directory Map

- `inbox/`: active task briefs that have not been completed or superseded.
- `working/`: optional notes for tasks currently in progress.
- `done/`: completion reports and validation summaries.
- `archive/inbox/`: completed, superseded, or historical task briefs.
- `output/`: historical files uploaded through the relay workflow.
- `templates/`: reusable task-brief templates.

## How Agents Select Instructions

1. Read the repository-root `AGENTS.md` and this file.
2. When the user gives a filename, open that exact file in `inbox/`.
3. When the user asks for the newest instructions, choose the newest Markdown
   file in `inbox/` by its sortable filename.
4. Never select a task from `archive/inbox/` unless the user explicitly asks
   to inspect historical instructions.
5. Check `done/` before repeating old work.

## Completion Bookkeeping

When a task requests relay bookkeeping, write a concise report to
`done/YYYY-MM-DD-task-name-report.md` and move the handled brief to
`archive/inbox/`. Keep generated project results in `results/`; use `output/`
only for historical relay artifacts or when a task explicitly requests a relay
copy.

Each completion report must briefly state:

- Which inbox instruction was implemented.
- What code was added or changed and its exact repository path.
- What results or artifacts were added or changed and their exact repository
  path.
- Which checks were run and whether they passed.
- Any remaining issue, or `None`.

## GitHub SSH And Push Policy

- Always use the local computer SSH credentials for GitHub operations.
- Keep the Git remote in SSH form: `git@github.com:OWNER/REPOSITORY.git`.
- Never switch the remote to HTTPS or request a personal access token when SSH is available.
- After finishing and verifying any requested change, review the diff, commit only the intended files, and immediately push the current branch to GitHub. Do not wait for a separate push request.
- Preserve unrelated user changes and do not include them in the task commit.
- Never force-push unless the user explicitly requests it.
- If the remote is missing, SSH authentication fails, the push is rejected, or branch protection blocks the push, report the exact blocker instead of bypassing it.

Never place credentials, SSH keys, access tokens, passwords, or session data in
this directory.
