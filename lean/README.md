# AlethfeldLean

A Lean 4 library of formalized mathematical proofs developed using the Alethfeld system.

## Quick Start

```bash
cd lean
lake build
```

## Library Structure

The library is organized by mathematical domain:

```
AlethfeldLean/
├── QBF/
│   └── Rank1/          # Quantum Boolean Function rank-1 results (fully verified)
```

## Verified Results

- **QBF Rank-1 Master Theorem**: Entropy-influence bound for rank-1 QBFs (0 sorries across all lemmas)

See `lean/API.md` for full documentation of available lemmas and their proofs.
