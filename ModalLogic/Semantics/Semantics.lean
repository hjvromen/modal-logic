/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Kripke Semantics for Modal Logic

This file defines the semantic notions for modal logic that build on Kripke frames:
- **Forcing relation**: when a formula is true at a world in a model
- **Validity**: when a formula is true in all models or frame classes
- **Semantic consequence**: when a formula follows from assumptions in all models

The core frame structure and frame properties are defined in
`ModalLogic.Semantics.Frame`.

## References

- Blackburn, de Rijke, Venema. *Modal Logic*. Cambridge University Press, 2001.
-/

import ModalLogic.Semantics.Frame
import ModalLogic.Syntax.ProofSystem

namespace Modal

open BasicModal

/-!
## Forcing Relation

The forcing relation `forces f v w φ` defines when formula φ is true at world w
in frame f under valuation v.
-/

/-- Forcing relation for basic modal formulas. -/
def forces (f : Frame.{0}) (v : Nat → f.states → Prop)
    (w : f.states) : Form → Prop
  | .bot => False
  | .var n => v n w
  | .and φ ψ => forces f v w φ ∧ forces f v w ψ
  | .impl φ ψ => forces f v w φ → forces f v w ψ
  | .box φ => ∀ u, f.rel w u → forces f v u φ

/-!
## Forcing Simp Lemmas
-/

@[simp] theorem forces_bot (f : Frame.{0}) (v : ℕ → f.states → Prop) (w : f.states) :
    forces f v w .bot ↔ False := by rfl

@[simp] theorem forces_var (f : Frame.{0}) (v : ℕ → f.states → Prop) (w : f.states) (n : ℕ) :
    forces f v w (.var n) ↔ v n w := by rfl

@[simp] theorem forces_and (f : Frame.{0}) (v : ℕ → f.states → Prop) (w : f.states) (φ ψ : Form) :
    forces f v w (.and φ ψ) ↔ forces f v w φ ∧ forces f v w ψ := by rfl

theorem forces_impl (f : Frame.{0}) (v : ℕ → f.states → Prop) (w : f.states) (φ ψ : Form) :
    forces f v w (.impl φ ψ) = (forces f v w φ → forces f v w ψ) := by rfl

@[simp] theorem forces_box (f : Frame.{0}) (v : ℕ → f.states → Prop) (w : f.states) (φ : Form) :
    forces f v w (.box φ) ↔ ∀ u, f.rel w u → forces f v u φ := by rfl

/-!
## Validity Notions
-/

/-- **Frame validity**: φ is valid in frame f (true at all worlds under all valuations). -/
def fValid (φ : Form) (f : Frame.{0}) : Prop :=
  ∀ (v : ℕ → f.states → Prop) (w : f.states), forces f v w φ

/-- **Frame class validity**: φ is valid in all frames of class C. -/
def FValid (φ : Form) (C : Set Frame.{0}) : Prop :=
  ∀ f ∈ C, fValid φ f

/-- **Global semantic consequence**: φ follows from AX in all frames. -/
def globalSemCsq (AX : Ctx) (φ : Form) : Prop :=
  ∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ ψ, ∀ x, ψ ∈ AX → forces F v x ψ) → ∀ x, forces F v x φ

end Modal
