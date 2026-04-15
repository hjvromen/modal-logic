/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Modal Logic: Correspondence Theory

This file proves the basic correspondence results between modal axioms and
frame properties, using the shared frame definitions from `ModalLogic.Semantics.Frame`.
-/

import ModalLogic.Semantics.Frame
import Mathlib.Tactic

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
