/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen
-/

/-
# Completeness Overview

This is a documentation-only file describing the completeness proof strategy.
The actual implementation is in:
- `ModalLogic.Metatheory.Maximal` — Maximal consistent sets and Lindenbaum's lemma
- `ModalLogic.Metatheory.Canonical` — Canonical model construction
- `ModalLogic.Metatheory.MaximalHelpers` — Helper lemmas for maximal consistent sets
-/

/-!
# Completeness for Modal Logic K

## Strategy Overview

To prove completeness (⊨ φ implies ⊢ φ), we use proof by contrapositive:
1. Assume ⊬ φ (φ is not provable)
2. Show ⊭ φ (φ is not valid)

The construction:
1. **Consistent set**: {¬φ} is consistent (otherwise ⊢ φ)
2. **Maximal extension**: Extend to maximal consistent set via Lindenbaum's lemma
3. **Canonical model**: Build model where worlds are maximal consistent sets
4. **Truth lemma**: In canonical model, w ⊩ ψ iff ψ ∈ w
5. **Countermodel**: ¬φ ∈ w, so w ⊮ φ, hence ⊭ φ

## Key Components

### Maximal Consistent Sets

A set Γ is **maximal consistent** if:
- **Consistent**: No contradiction derivable from Γ
- **Maximal**: For all φ, either φ ∈ Γ or ¬φ ∈ Γ

**Lindenbaum's Lemma**: Every consistent set extends to a maximal consistent set.

### Canonical Model

The **canonical model** M_can has:
- **Worlds**: Maximal consistent sets
- **Accessibility**: Γ R Δ iff for all □ψ ∈ Γ, we have ψ ∈ Δ
- **Valuation**: V(p) = {Γ : p ∈ Γ}

### Completeness Theorem

**Main Result**: If ⊨ φ then ⊢ φ (by contrapositive as outlined above)
-/
