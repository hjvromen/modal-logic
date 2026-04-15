/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Modal Logic: Kripke Semantics and Correspondence Theory
-/

import Mathlib.Tactic

namespace Modal

/-- A Kripke frame: a type of states together with an accessibility relation. -/
structure Frame where
  states : Type*
  rel : states → states → Prop

namespace Frame

variable {f : Frame}

/-- Box modality: `box φ w` iff `φ` holds at all accessible worlds. -/
def box (φ : f.states → Prop) (w : f.states) : Prop :=
  ∀ v, f.rel w v → φ v

/-- Diamond modality: `diamond φ w` iff `φ` holds at some accessible world. -/
def diamond (φ : f.states → Prop) (w : f.states) : Prop :=
  ∃ v, f.rel w v ∧ φ v

/-- Negation (pointwise). -/
def neg (φ : f.states → Prop) (w : f.states) : Prop := ¬ φ w

/-- Conjunction (pointwise). -/
def conj (φ ψ : f.states → Prop) (w : f.states) : Prop := φ w ∧ ψ w

/-- Implication (pointwise). -/
def impl (φ ψ : f.states → Prop) (w : f.states) : Prop := φ w → ψ w

/-- Validity: `φ` holds at every world. -/
def valid (φ : f.states → Prop) : Prop := ∀ w, φ w

/-! ## Frame Properties -/

/-- A frame is reflexive: `∀ w, R w w`. -/
def Reflexive (f : Frame) : Prop := ∀ (x : f.states), f.rel x x

/-- A frame is transitive. Uses `{}` so that `fun h1 h2 => ...` works. -/
def Transitive (f : Frame) : Prop :=
  ∀ {a b c : f.states}, f.rel a b → f.rel b c → f.rel a c

/-- A frame is symmetric if `R w v → R v w`. -/
def Symmetric (f : Frame) : Prop :=
  ∀ {w v : f.states}, f.rel w v → f.rel v w

/-- A frame is Euclidean if `R w u → R w v → R u v`. -/
def Euclidean (f : Frame) : Prop :=
  ∀ {w u v : f.states}, f.rel w u → f.rel w v → f.rel u v

/-- A frame is serial if every world has a successor. -/
def Serial (f : Frame) : Prop := ∀ (x : f.states), ∃ y, f.rel x y

end Frame

end Modal

/-- A relation is serial if every element has a successor. -/
def Serial {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ x, ∃ y, r x y

/-! ## Correspondence Theory -/

theorem T_of_Reflexive {f : Modal.Frame} (hR : Modal.Frame.Reflexive f) (φ : f.states → Prop)
    (w : f.states) : Modal.Frame.box φ w → φ w :=
  fun h => h w (hR w)

theorem Four_of_Transitive {f : Modal.Frame} (hR : Modal.Frame.Transitive f) (φ : f.states → Prop)
    (w : f.states) : Modal.Frame.box φ w → Modal.Frame.box (Modal.Frame.box φ) w :=
  fun h _u hwu _v huv => h _v (hR hwu huv)

theorem B_of_Symmetric {f : Modal.Frame} (hR : Modal.Frame.Symmetric f) (φ : f.states → Prop)
    (w : f.states) : φ w → Modal.Frame.box (Modal.Frame.diamond φ) w :=
  fun hw _v hwv => ⟨w, hR hwv, hw⟩

theorem Five_of_Euclidean {f : Modal.Frame} (hR : Modal.Frame.Euclidean f) (φ : f.states → Prop)
    (w : f.states) : Modal.Frame.diamond φ w → Modal.Frame.box (Modal.Frame.diamond φ) w :=
  fun ⟨u, hwu, hu⟩ _v hwv => ⟨u, hR hwv hwu, hu⟩
