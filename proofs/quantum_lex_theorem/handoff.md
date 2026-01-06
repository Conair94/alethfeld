# Quantum Entropy Increase Theorem - Handoff Document

**Date:** 2026-01-06
**Status:** In Progress - 6 sorries remaining in Lean formalization

## Overview

This document provides a comprehensive handoff for the ongoing work on proving the Quantum Entropy Increase Theorem (Theorem 1) in Lean 4 with no sorries.

## Goal

From `ralph-prompt.md`:
- Execute the Alethfeld protocol to prove Theorem 1
- Prove all lemmas and theorem in Lean with **NO sorries** and **NO cheating axiomatizing**
- Output `<promise>COMPLETE</promise>` when done

## Current State

### Lean File Location
`/home/tobiasosborne/Projects/alethfeld/lean/AlethfeldLean/Quantum/EntropyIncrease.lean`

### Sorry Count: 6 (down from 7)

| Line | Lemma/Theorem | Status | Difficulty |
|------|---------------|--------|------------|
| 534 | `fourier_inversion` | Sorry | Medium - needs character completeness |
| 911 | `pauliCoeff_diagonalObs_Z_S` | Sorry | Medium - needs bijection lemmas |
| 946 | `diagonalObs_spectralEntropy_eq` | Sorry | Hard - depends on above |
| 953 | `diagonalObs_quantumInfluence_eq` | Sorry | Hard - depends on above |
| 960 | `th_transform_entropy_increase` | Sorry | Hard - needs Kronecker power infra |
| 969 | `th_transform_influence_preserved` | Sorry | Hard - needs Kronecker power infra |

### Completed Proofs

1. **`pauliString_diag_zero_of_XY`** (lines 262-280)
   - Proves pauliString has zero diagonal if any component is X or Y
   - Key for showing Pauli coefficients vanish for non-Z indices

2. **`pauliCoeff_diagonalObs_nonZ`** (lines 759-789)
   - Proves Pauli coefficient of diagonal observable is zero for non-Z_S indices
   - Uses `pauliString_diag_zero_of_XY` and diagonal matrix properties

3. **`character_completeness`** (lines 378-524) - **PARTIAL**
   - The x = y case is fully proved
   - The x ≠ y case has the correct structure (involution argument) but technical issues remain
   - Errors in lines 428, 437, 465, 468, 471, 490, 503

### In-Progress Work

#### Character Completeness Lemma (lines 378-524)

The lemma states:
```lean
lemma character_completeness {n : ℕ} (x y : Fin n → Bool) :
    (∑ S : Finset (Fin n), (parityFunc S x : ℂ) * (parityFunc S y : ℂ)) =
      if x = y then (2 : ℂ)^n else 0
```

**Proof Strategy:**
- x = y case: Each term is χ_S(x)² = 1, sum = 2^n (number of subsets) ✓ DONE
- x ≠ y case: Use `Finset.sum_involution` with φ(S) = S ∆ {i} where i is a position where x and y differ

**Technical Issues:**
1. Line 428: `simp_all` doesn't close goal in inr case
2. Lines 437, 471: Trivial modular arithmetic goals not closing
3. Line 465: Type mismatch with `h'` and `hi_in`
4. Lines 468-469: omega can't prove and "no goals" error
5. Lines 490, 503: `h_card_change` not being used correctly as a function

**Root Cause:** The `h_card_change` lemma is parameterized by `z : Fin n → Bool` but the proof tries to specialize it incorrectly. Need to restructure the case analysis.

## Key Definitions

### Core Types
```lean
def BoolFunc (n : ℕ) := (Fin n → Bool) → ℤ  -- Boolean function {0,1}^n → {±1}
def parityFunc {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : ℤ  -- χ_S(x)
noncomputable def fourierCoeff {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) : ℝ
noncomputable def diagonalObs {n : ℕ} (f : BoolFunc n) : QubitMat n  -- L_f
```

### Pauli Operators
```lean
noncomputable def pauliZ_S {n : ℕ} (S : Finset (Fin n)) : QubitMat n  -- Z at S, I elsewhere
noncomputable def pauliX_S {n : ℕ} (S : Finset (Fin n)) : QubitMat n  -- X at S, I elsewhere
```

## Dependencies

### Required Infrastructure (Not Yet Built)
1. **Kronecker powers**: `kroneckerPow n M` for n-fold tensor product
2. **Bijection lemmas**: Connection between `Fin (2^n)` and `Fin n → Bool` via testBit
3. **Trace of Kronecker products**: `trace (A ⊗ B) = trace A * trace B`

### Available from Pauli.lean
- `pauliString` - n-fold tensor product of Pauli matrices
- `trace_pauliString` - Trace is 2^n if all identity, 0 otherwise
- `finPow2SuccEquiv` - Equivalence between Fin (2^(n+1)) and Fin (2^n) × Fin 2

## Recommended Next Steps

### Priority 1: Fix `character_completeness`
1. Restructure the x ≠ y case to properly use h_card_change
2. Alternative: Prove a simpler `parityFunc_symmDiff_parity` lemma first
3. The mathematical argument is sound; issues are purely technical

### Priority 2: Prove `fourier_inversion`
Once character_completeness works:
```lean
lemma fourier_inversion {n : ℕ} (f : BoolFunc n) (x : Fin n → Bool) :
    (f x : ℂ) = ∑ S : Finset (Fin n), (fourierCoeff f S : ℂ) * (parityFunc S x : ℂ)
```
Proof outline:
1. Expand fourierCoeff definition
2. Swap sums
3. Apply character_completeness
4. Only the y = x term survives

### Priority 3: Prove `pauliCoeff_diagonalObs_Z_S`
```lean
lemma pauliCoeff_diagonalObs_Z_S {n : ℕ} (f : BoolFunc n) (S : Finset (Fin n)) :
    pauliCoeff (diagonalObs f) (fun i => if i ∈ S then 3 else 0) = (fourierCoeff f S : ℂ)
```
Requires:
- Connection between testBit and Bool function representation
- Trace computation through diagonal matrices

### Priority 4: Remaining Theorems
- `diagonalObs_spectralEntropy_eq` and `diagonalObs_quantumInfluence_eq` follow from above
- `th_transform_entropy_increase` and `th_transform_influence_preserved` need Kronecker power infrastructure

## File Structure

```
proofs/quantum_lex_theorem/
├── quantum_lex_theorem.md   # Main theorem statement
├── lemma1.edn through lemma6.edn  # EDN proof graphs
├── theorem1.edn             # Main theorem EDN
├── proof.tex                # LaTeX document
├── proof.pdf                # Compiled proof
└── handoff.md               # This file

lean/AlethfeldLean/Quantum/
├── Basic.lean               # Core quantum definitions
├── Pauli.lean               # Pauli matrices and pauliString
└── EntropyIncrease.lean     # Main theorem (820+ lines)
```

## Mathematical Background

### Theorem 1: Quantum Entropy Increase
For a Boolean function f: {0,1}^n → {±1}, the TH transformation (T⊗ⁿ H⊗ⁿ) applied to the diagonal observable L_f satisfies:

1. **Entropy Increase**: H(TH · L_f) = H(L_f) + Inf(L_f)
2. **Influence Preservation**: Inf(TH · L_f) = Inf(L_f)

Where:
- H(·) is spectral entropy
- Inf(·) is total influence (sum of Fourier weights times subset sizes)
- L_f is the diagonal matrix with f(x) on diagonal

### Key Lemmas
1. **Diagonal Pauli Expansion**: L_f = Σ_S f̂(S) Z_S
2. **Hadamard Conjugation**: H Z H† = X
3. **T Gate Conjugation**: T X T† splits into uniform superposition
4. **T Expansion**: Maps X_S to 2^|S| terms of equal magnitude
5. **Weight Preservation**: Product unitaries preserve Pauli weight
6. **Entropy of Uniform Splitting**: Entropy increases by log(k) when splitting into k equal parts

## Notes for Next Session

1. The `character_completeness` proof is ~150 lines and structurally correct but has technical bugs
2. Consider using `native_decide` or `decide` for finite case analysis
3. The `Finset.sum_involution` API requires careful argument ordering
4. All EDN proofs and LaTeX are complete; only Lean formalization remains
5. The git status shows uncommitted changes in `.claude/` hooks and scripts

## Commands to Resume

```bash
cd /home/tobiasosborne/Projects/alethfeld
# Check current sorry count
grep -n "sorry" lean/AlethfeldLean/Quantum/EntropyIncrease.lean | wc -l
# Run Lean type checker
lake build AlethfeldLean.Quantum.EntropyIncrease
```
