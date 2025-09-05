# Contributing

Thank you for your interest in contributing! This project is a mathlib-only Lean 4 development. Please follow these rails to keep the proof track stable.

## Branching strategy
- Feature work: `feat/<short-topic>` (e.g., `feat/embedding`).
- Chores/docs/CI: `chore/<topic>` (e.g., `chore/ci-docs`).
- Fixes within a track: `fix(track-<name>): <short>` as the first line of the commit message.
- One branch per agent/task. If a change requires touching shared interfaces, open a minimal “interface PR” first and get sign-off before proceeding.

## File ownership and scope
- Only edit files within your assigned tracks. Do not modify shared core types unless agreed via an interface PR.
- Do not introduce axioms or `sorry`.
- If a deep lemma is missing from mathlib and is required, add a one-line note to `BLOCKERS.md` and stop. Do not add local axioms.

## Build and verification
- Build locally with:
  ```bash
  lake update && lake build
  bash scripts/verify.sh
  ```
- CI runs `lake build` and `scripts/verify.sh` and fails on holes/axioms.

## Interface PR protocol
- If your change requires altering a shared interface (types, names, or signatures used outside your track):
  1. Open a small PR labeled `interface` that only introduces the minimal signature/structure changes.
  2. Include a short rationale and a migration note for downstream modules.
  3. After approval, rebase your feature branch and proceed with implementation.

## Blocker policy
- If you encounter a missing deep lemma in mathlib, record:
  - one sentence in `BLOCKERS.md` describing the needed statement and a reference
  - optional: a short Lean sketch showing where it blocks
- Then stop work on that path and open an issue linking the blocker entry.

## Code style
- Keep code readable and idiomatic. Prefer descriptive names, early returns, and minimal nesting.
- Avoid unused variables and unreachable tactics. Prefer `simp` over `simpa` when possible.
- Public names and signatures should be stable and documented with short docstrings.

## Tests and examples
- Add small examples in `ym/Examples.lean` (or sibling example files) to demonstrate interfaces or new adapters.
- Ensure examples build under CI.

## PR checklist
- [ ] Builds locally and passes `scripts/verify.sh`
- [ ] No new axioms/sorries
- [ ] Docs updated (README/AGENTS or module docstrings as appropriate)
- [ ] Interface PR merged first if shared changes were needed
