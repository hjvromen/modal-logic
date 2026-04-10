/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Completeness Module

This file imports all completeness-related components of the modal logic formalization.

## Contents

- **Maximal**: Maximal consistent sets and Lindenbaum's lemma
- **Canonical**: Canonical model construction
- **MaximalHelpers**: Helper lemmas for maximal consistent sets
-/

import ModalLogic.Metatheory.Maximal
import ModalLogic.Metatheory.Canonical
import ModalLogic.Metatheory.MaximalHelpers
import ModalLogic.Metatheory.CompletenessKDKB
import ModalLogic.Metatheory.CompletenessCube
import ModalLogic.Metatheory.CompletenessD5

/-!
# Completeness for Modal Logic K

This module establishes the completeness of System K through the canonical model method.

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
- Proved using Zorn's lemma on the poset of consistent extensions
- Critical use of classical logic (axiom of choice)

### Canonical Model

The **canonical model** M_can has:
- **Worlds**: Maximal consistent sets W = {Γ : Γ is max consistent}
- **Accessibility**: Γ R Δ iff for all □ψ ∈ Γ, we have ψ ∈ Δ
- **Valuation**: V(p) = {Γ : p ∈ Γ}

**Truth Lemma**: For all worlds Γ and formulas φ:
  M_can, Γ ⊩ φ iff φ ∈ Γ

Proved by structural induction on φ. The modal case uses:
- (→): If □φ ∈ Γ and Γ R Δ, then φ ∈ Δ by definition of R
- (←): If ∀Δ. Γ R Δ → φ ∈ Δ, then □φ ∈ Γ by maximality

### Completeness Theorem

**Main Result**: If ⊨ φ then ⊢ φ

**Proof**: Contrapositive. If ⊬ φ:
1. Then {¬φ} is consistent
2. Extend to maximal Γ with ¬φ ∈ Γ
3. By truth lemma: M_can, Γ ⊮ φ
4. Therefore ⊭ φ

## Decidability

**Key Property**: Maximal consistent sets are decidable:
  For all φ, either φ ∈ Γ or ¬φ ∈ Γ

This is the **law of excluded middle** for maximal theories.

## Applications

Completeness enables:
- Model checking: Check validity by checking provability
- Decidability results: K is decidable (finite model property)
- Automated reasoning: Proof search guided by semantics
-/
