import ModalLogic.Semantics.Definability

/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen
-/

/-!
# Undefinability and Invariance under Surjective Bounded Morphisms

This file establishes fundamental invariance properties of modal logic and proves
undefinability results for certain frame classes.

## Main Results

- `invarianceDunion`: Theories are preserved under disjoint union (left component)
- `invarianceGenSubmodel`: Theories are preserved under generated submodels
- `invarianceBisim`: Bisimilar points have identical modal theories
- `pullBack`: Surjective bounded morphisms pull back counterexamples
- `invariancePullBack`: If F contains f1 but not its bounded morphism image f2, then F is undefinable
-/

namespace Modal
open BasicModal
open BasicModal.Modal
open ModalPath

------------------------------------------------------------------------------
-- § 1. Undefinability and Theory at a Point
------------------------------------------------------------------------------

/-- A class of frames F is undefinable if no formula defines it. -/
def undefinable (F : Set Frame.{0}) : Prop :=
  ∀ φ, ¬ BasicModal.Defines φ F

/-- The set of all formulas true at a given world. -/
def theoryAt (f : Frame) (v : Nat → f.states → Prop) (x : f.states) : Set Form :=
  { φ : Form | forces f v x φ }

------------------------------------------------------------------------------
-- § 2. Disjoint Union of Frames
------------------------------------------------------------------------------

/-- Accessibility in disjoint union: within-component only. -/
def dunionRel {α β : Type} (r1 : α → α → Prop) (r2 : β → β → Prop) :
    Sum α β → Sum α β → Prop
  | .inl a1, .inl a2 => r1 a1 a2
  | .inr b1, .inr b2 => r2 b1 b2
  | _, _ => False

/-- Valuation for disjoint union. -/
def valDunion {f1 f2 : Frame} (v1 : Nat → f1.states → Prop)
    (v2 : Nat → f2.states → Prop) : Nat → Sum f1.states f2.states → Prop
  | n, .inl x1 => v1 n x1
  | n, .inr x2 => v2 n x2

/-- Disjoint union of frames. -/
def frameDunion (f1 f2 : Frame) : Frame where
  states := Sum f1.states f2.states
  rel := dunionRel f1.rel f2.rel

/-- Theories are preserved in the left component of a disjoint union. -/
theorem invarianceDunion (f1 f2 : Frame) (v1 : Nat → f1.states → Prop)
    (v2 : Nat → f2.states → Prop) (x1 : f1.states) :
    theoryAt f1 v1 x1 = theoryAt (frameDunion f1 f2) (valDunion v1 v2) (.inl x1) := by
  ext φ
  revert x1
  induction φ with
  | bot => intro x1; rfl
  | var n => intro x1; rfl
  | and φ ψ ih_φ ih_ψ =>
      intro x1
      constructor
      · intro h; exact ⟨(ih_φ x1).mp h.1, (ih_ψ x1).mp h.2⟩
      · intro h; exact ⟨(ih_φ x1).mpr h.1, (ih_ψ x1).mpr h.2⟩
  | impl φ ψ ih_φ ih_ψ =>
      intro x1
      constructor
      · intros h h1; exact (ih_ψ x1).mp (h ((ih_φ x1).mpr h1))
      · intros h h1; exact (ih_ψ x1).mpr (h ((ih_φ x1).mp h1))
  | box φ ih_φ =>
      intro x1
      constructor
      · intros h S h1
        cases S with
        | inl S => exact (ih_φ S).mp (h S h1)
        | inr S => exact False.elim h1
      · intros h S h1
        exact (ih_φ S).mpr (h (.inl S) h1)

------------------------------------------------------------------------------
-- § 3. Generated Submodels
------------------------------------------------------------------------------

/-- Generated subframe from a point. -/
def frameGenSubframe (f : Frame) (x : f.states) : Frame where
  states := { y // Reachable f.rel x y }
  rel := fun x1 x2 => f.rel x1.val x2.val

/-- Valuation for generated subframe. -/
def valGenSubframe (f : Frame) (x : f.states) (v : Nat → f.states → Prop) :
    Nat → (frameGenSubframe f x).states → Prop :=
  fun n y => v n y.val

/-- Theories are preserved in generated submodels. -/
theorem invarianceGenSubmodel (f : Frame) (v : Nat → f.states → Prop)
    (x : f.states) (y : (frameGenSubframe f x).states) :
    theoryAt f v y.val = theoryAt (frameGenSubframe f x) (valGenSubframe f x v) y := by
  ext φ
  revert y
  induction φ with
  | bot => intro y; rfl
  | var n => intro y; rfl
  | and φ ψ ih_φ ih_ψ =>
      intro y
      constructor
      · intro h; exact ⟨(ih_φ y).mp h.1, (ih_ψ y).mp h.2⟩
      · intro h; exact ⟨(ih_φ y).mpr h.1, (ih_ψ y).mpr h.2⟩
  | impl φ ψ ih_φ ih_ψ =>
      intro y
      constructor
      · intros h1 h2; exact (ih_ψ y).mp (h1 ((ih_φ y).mpr h2))
      · intros h1 h2; exact (ih_ψ y).mpr (h1 ((ih_φ y).mp h2))
  | box φ ih_φ =>
      intro y
      constructor
      · intros h1 z h2
        exact (ih_φ z).mp (h1 z.val h2)
      · intros h1 z h2
        have h3 : Reachable f.rel x z :=
          reachRight (R := f.rel) (x := x) (y := y.1) (z := z) y.2 h2
        exact (ih_φ ⟨z, h3⟩).mpr (h1 ⟨z, h3⟩ h2)

------------------------------------------------------------------------------
-- § 4. Bisimulation
------------------------------------------------------------------------------

/-- Atomic base condition: bisimilar states agree on variables. -/
def bisimBase {f1 f2 : Frame} (v1 : Nat → f1.states → Prop)
    (v2 : Nat → f2.states → Prop) (x1 : f1.states) (x2 : f2.states) : Prop :=
  ∀ n, v1 n x1 ↔ v2 n x2

/-- Forth condition: every move from x1 can be matched from x2. -/
def bisimForth {f1 f2 : Frame} (bisim : f1.states → f2.states → Prop)
    (x1 : f1.states) (x2 : f2.states) : Prop :=
  ∀ y1, f1.rel x1 y1 → ∃ y2, f2.rel x2 y2 ∧ bisim y1 y2

/-- Back condition: every move from x2 can be matched from x1. -/
def bisimBack {f1 f2 : Frame} (bisim : f1.states → f2.states → Prop)
    (x1 : f1.states) (x2 : f2.states) : Prop :=
  ∀ y2, f2.rel x2 y2 → ∃ y1, f1.rel x1 y1 ∧ bisim y1 y2

/-- Full bisimulation: base + forth + back at every related pair. -/
def isBisimulation {f1 f2 : Frame} (v1 : Nat → f1.states → Prop)
    (v2 : Nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop) : Prop :=
  ∀ x1 x2, bisim x1 x2 →
    bisimBase v1 v2 x1 x2 ∧ bisimForth bisim x1 x2 ∧ bisimBack bisim x1 x2

/-- Bisimilar points have the same modal theory. -/
theorem invarianceBisim {f1 f2 : Frame} (v1 : Nat → f1.states → Prop)
    (v2 : Nat → f2.states → Prop) (bisim : f1.states → f2.states → Prop)
    (h : isBisimulation v1 v2 bisim) (x1 : f1.states) (x2 : f2.states) :
    bisim x1 x2 → theoryAt f1 v1 x1 = theoryAt f2 v2 x2 := by
  intro h1
  ext φ
  revert x1 x2
  induction φ with
  | bot => intros x1 x2 h1; rfl
  | var n =>
      intros x1 x2 h1
      constructor
      · intro h2; exact (h x1 x2 h1).1 n |>.mp h2
      · intro h2; exact (h x1 x2 h1).1 n |>.mpr h2
  | and φ ψ ih_φ ih_ψ =>
      intros x1 x2 h1
      constructor
      · intro h2; exact ⟨(ih_φ x1 x2 h1).mp h2.1, (ih_ψ x1 x2 h1).mp h2.2⟩
      · intro h2; exact ⟨(ih_φ x1 x2 h1).mpr h2.1, (ih_ψ x1 x2 h1).mpr h2.2⟩
  | impl φ ψ ih_φ ih_ψ =>
      intros x1 x2 h1
      constructor
      · intros h2 h3; exact (ih_ψ x1 x2 h1).mp (h2 ((ih_φ x1 x2 h1).mpr h3))
      · intros h2 h3; exact (ih_ψ x1 x2 h1).mpr (h2 ((ih_φ x1 x2 h1).mp h3))
  | box φ ih_φ =>
      intros x1 x2 h1
      obtain ⟨_, h_forth, h_back⟩ := h x1 x2 h1
      constructor
      · intros h2 y2 h3
        obtain ⟨y1, h6, h7⟩ := h_back y2 h3
        exact (ih_φ y1 y2 h7).mp (h2 y1 h6)
      · intros h2 y1 h3
        obtain ⟨y2, h5, h7⟩ := h_forth y1 h3
        exact (ih_φ y1 y2 h7).mpr (h2 y2 h5)

------------------------------------------------------------------------------
-- § 5. Bounded Morphisms
------------------------------------------------------------------------------

/-- A function preserving and reflecting accessibility. -/
def isBddMorphism {f1 f2 : Frame} (g : f1.states → f2.states) : Prop :=
  ∀ x1, bisimForth (fun x1 x2 => g x1 = x2) x1 (g x1) ∧
         bisimBack (fun x1 x2 => g x1 = x2) x1 (g x1)

/-- A bounded morphism that's onto. -/
def isSurjBddMorphism {f1 f2 : Frame} (g : f1.states → f2.states) : Prop :=
  Function.Surjective g ∧ isBddMorphism g

/-- Surjective bounded morphisms pull back counterexamples. -/
theorem pullBack {f1 f2 : Frame} (g : f1.states → f2.states)
    (h : isSurjBddMorphism g) (φ : Form) :
    ¬ fValid φ f2 → ¬ fValid φ f1 := by
  classical
  intro hnot2
  have h0 : ¬ ∀ v2, ∀ y : f2.states, forces f2 v2 y φ := by
    simpa [fValid] using hnot2
  obtain ⟨v2, h1⟩ := not_forall.mp h0
  obtain ⟨y, hcounter⟩ := not_forall.mp h1
  let v1 := fun n x => v2 n (g x)
  obtain ⟨hsurj, hbdd⟩ := h
  obtain ⟨x, hx⟩ := hsurj y
  have h_bisim : isBisimulation v1 v2 (fun x y => g x = y) := by
    intro x1 x2 hEq
    subst hEq
    exact ⟨(fun _ => ⟨id, id⟩), (hbdd x1).1, (hbdd x1).2⟩
  have h_th : theoryAt f1 v1 x = theoryAt f2 v2 (g x) :=
    invarianceBisim v1 v2 (fun x y => g x = y) h_bisim x (g x) rfl
  intro hvalid1
  have hx_mem : φ ∈ theoryAt f1 v1 x := hvalid1 v1 x
  have hy_mem' : φ ∈ theoryAt f2 v2 (g x) := by rw [← h_th]; exact hx_mem
  have hy_mem : φ ∈ theoryAt f2 v2 y := by subst hx; exact hy_mem'
  exact hcounter hy_mem

------------------------------------------------------------------------------
-- § 6. Undefinability via Bounded Morphisms
------------------------------------------------------------------------------

/-- If F contains f1 but not its bounded morphism image f2, then F is undefinable. -/
lemma invariancePullBack (F : Set Frame.{0}) {f1 f2 : Frame}
    (hf1 : f1 ∈ F) (hf2 : f2 ∉ F)
    (h : ∃ g : f1.states → f2.states, isSurjBddMorphism g) :
    undefinable F := by
  classical
  rcases h with ⟨g, hg⟩
  intro φ hdef
  have h1 : fValid φ f1 := (hdef f1).mp hf1
  have hnot2 : ¬ fValid φ f2 := mt (hdef f2).mpr hf2
  exact (pullBack g hg φ) hnot2 h1

end Modal
