/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Kripke Frames for Modal Logic

This file defines the core semantic structures shared across the modal logic formalization:
- **Kripke frames**: structures with worlds and an accessibility relation
- **Frame operations**: box, diamond, negation, conjunction, implication, validity
- **Frame properties**: reflexivity, symmetry, transitivity, Euclidean, seriality

## References

- Blackburn, de Rijke, Venema. *Modal Logic*. Cambridge University Press, 2001.
-/

universe u

/-- A single-agent Kripke frame. -/
structure Modal.Frame where
  states : Type u
  rel : states → states → Prop

namespace Modal.Frame

variable {f : Modal.Frame.{u}}

/-- Box modality: φ holds at all accessible worlds. -/
def box (φ : f.states → Prop) (w : f.states) : Prop :=
  ∀ v, f.rel w v → φ v

/-- Diamond modality: φ holds at some accessible world. -/
def diamond (φ : f.states → Prop) (w : f.states) : Prop :=
  ∃ v, f.rel w v ∧ φ v

/-- Implication of predicates. -/
def impl (φ ψ : f.states → Prop) (w : f.states) : Prop :=
  φ w → ψ w

/-- Conjunction of predicates. -/
def conj (φ ψ : f.states → Prop) (w : f.states) : Prop :=
  φ w ∧ ψ w

/-- Negation of a predicate. -/
def neg (φ : f.states → Prop) (w : f.states) : Prop :=
  ¬ φ w

/-- Validity: φ holds at every world. -/
def valid (φ : f.states → Prop) : Prop :=
  ∀ w, φ w

end Modal.Frame

/-- Reflexive frame property: every world can access itself. -/
def Modal.Frame.Reflexive (f : Modal.Frame) : Prop :=
  ∀ w, f.rel w w

/-- Symmetric frame property: if `R w v` then `R v w`. -/
def Modal.Frame.Symmetric (f : Modal.Frame) : Prop :=
  ∀ {w v}, f.rel w v → f.rel v w

/-- Transitive frame property: if `R w v` and `R v u` then `R w u`. -/
def Modal.Frame.Transitive (f : Modal.Frame) : Prop :=
  ∀ {w v u}, f.rel w v → f.rel v u → f.rel w u

/-- Euclidean frame property: if `R w v` and `R w u` then `R v u`. -/
def Modal.Frame.Euclidean (f : Modal.Frame) : Prop :=
  ∀ {w v u}, f.rel w v → f.rel w u → f.rel v u

/-- Serial frame property: every world has at least one successor. -/
def Modal.Frame.Serial (f : Modal.Frame) : Prop :=
  ∀ w, ∃ v, f.rel w v
