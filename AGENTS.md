# Agent Instructions

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

## Current Status: QBF Rank-1 Proofs Complete

**Status:** ✅ ALL LEMMAS VERIFIED (0 sorries)

The QBF Rank-1 project is complete. All lemmas L1-L5 are fully verified:

| Lemma | File | Status |
|-------|------|--------|
| L1 Fourier | `lean/AlethfeldLean/QBF/Rank1/L1Fourier.lean` | ✅ 0 sorries |
| L2 Influence | `lean/AlethfeldLean/QBF/Rank1/L2Influence.lean` | ✅ 0 sorries |
| L3 Entropy | `lean/AlethfeldLean/QBF/Rank1/L3Entropy.lean` | ✅ 0 sorries |
| Shannon Max | `lean/AlethfeldLean/QBF/Rank1/ShannonMax.lean` | ✅ 0 sorries |
| L4 Maximum | `lean/AlethfeldLean/QBF/Rank1/L4Maximum.lean` | ✅ 0 sorries |
| L5 Asymptotic | `lean/AlethfeldLean/QBF/Rank1/L5Asymptotic.lean` | ✅ 0 sorries |
| Master Theorem | `lean/AlethfeldLean/QBF/Rank1/QBFRank1MasterTheorem.lean` | ✅ 0 sorries |

**Next Agent's Priority:**
1. Check `bd ready` for available work
2. Run `lake build` to verify no regressions
3. See `lean/API.md` for full documentation

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1.  **File issues for remaining work** - Create issues for anything that needs follow-up
2.  **Run quality gates** (if code changed) - Tests, linters, builds
3.  **Update issue status** - Close finished work, update in-progress items
4.  **PUSH TO REMOTE** - This is MANDATORY:
    ```bash
    git pull --rebase
    bd sync
    git push
    git status  # MUST show "up to date with origin"
    ```
5.  **Clean up** - Clear stashes, prune remote branches
6.  **Verify** - All changes committed AND pushed
7.  **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds