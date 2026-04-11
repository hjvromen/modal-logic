/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Kripke Semantics

This file defines the forcing relation and validity notions for modal logic.
-/

import ModalLogic.Syntax.ProofSystem
import ModalLogic.Semantics.Correspondence

namespace Modal
open BasicModal

/-!
## § 1. Forcing Relation
-/

/-- **Forcing relation**: `forces F V w φ` means formula φ is true at world w
in model (F, V). Defined by structural recursion on φ. -/
def forces (F : Frame.{0}) (V : Nat → F.states → Prop) :
    F.states → Form → Prop
  | _, .bot      => False
  | w, .var n    => V n w
  | w, .and φ ψ  => forces F V w φ ∧ forces F V w ψ
  | w, .impl φ ψ => forces F V w φ → forces F V w ψ
  | w, .box φ    => ∀ v, F.rel w v → forces F V v φ

@[simp] lemma forces_and {F : Frame.{0}} {V : Nat → F.states → Prop} {w : F.states}
    {φ ψ : Form} : forces F V w (φ ⋏ ψ) ↔ forces F V w φ ∧ forces F V w ψ := Iff.rfl

@[simp] lemma forces_impl {F : Frame.{0}} {V : Nat → F.states → Prop} {w : F.states}
    {φ ψ : Form} : forces F V w (φ ⊃ ψ) ↔ (forces F V w φ → forces F V w ψ) := Iff.rfl

/-!
## § 2. Validity Notions
-/

/-- **Frame validity**: φ is valid in frame f if it holds at every world under every valuation. -/
def fValid (φ : Form) (f : Frame.{0}) : Prop :=
  ∀ (v : Nat → f.states → Prop) (x : f.states), forces f v x φ

/-- **Frame class validity**: φ is valid in frame class C if it is valid in every frame in C. -/
def FValid (φ : Form) (C : Set Frame.{0}) : Prop :=
  ∀ (F : Frame.{0}), F ∈ C → ∀ (v : Nat → F.states → Prop) (x : F.states), forces F v x φ

/-- **Global semantic consequence**: φ is a global semantic consequence of AX
if in every model where all axioms in AX hold everywhere, φ also holds everywhere. -/
def globalSemCsq (AX : Ctx) (φ : Form) : Prop :=
  ∀ (F : Frame.{0}) (v : Nat → F.states → Prop),
    (∀ ψ, ∀ x : F.states, ψ ∈ AX → forces F v x ψ) → ∀ x : F.states, forces F v x φ

end Modal
