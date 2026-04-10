/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Syntax Module

This file imports all syntax-related components of the modal logic formalization.

## Contents

- **Formula**: Core formula type with primitive constructors
- **Derived**: Derived logical operators (negation, disjunction, etc.)
- **ProofSystem**: Hilbert-style proof system K
- **BasicLemmas**: Fundamental lemmas about the proof system
- **SyntaxLemmas**: Additional syntactic properties and utilities
-/

import ModalLogic.Syntax.Formula
import ModalLogic.Syntax.Derived
import ModalLogic.Syntax.ProofSystem
import ModalLogic.Syntax.BasicLemmas
import ModalLogic.Syntax.SyntaxLemmas
import ModalLogic.Syntax.Experimental

/-!
# Modal Logic Syntax

This module provides the syntactic foundation for modal propositional logic.

## Formula Type

Formulas are built from five primitive constructors:
- `⊥` (bot): Falsity
- `var n`: Propositional variables
- `φ ∧ ψ` (and): Conjunction
- `φ → ψ` (impl): Implication
- `□φ` (box): Necessity

All other operators are derived:
- `¬φ := φ → ⊥`
- `⊤ := ¬⊥`
- `φ ∨ ψ := ¬φ → ψ`
- `φ ↔ ψ := (φ → ψ) ∧ (ψ → φ)`
- `◇φ := ¬□¬φ`

## Proof System K

The minimal normal modal logic with axioms:
- **PL1-PL6**: Classical propositional logic axioms
- **K**: □(φ → ψ) → (□φ → □ψ)

And inference rules:
- **Modus Ponens**: From φ and φ → ψ, derive ψ
- **Necessitation**: From φ, derive □φ

## Key Results

- Identity: ⊢ φ → φ
- Deduction theorem: Γ ∪ {φ} ⊢ ψ iff Γ ⊢ φ → ψ
- Weakening: Γ ⊢ φ implies Γ ∪ Δ ⊢ φ
- Cut elimination (implicit in derivability)
-/
