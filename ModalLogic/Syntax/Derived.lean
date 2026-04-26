/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Derived Operators for Modal Logic

This file defines the derived logical operators that can be expressed
in terms of the primitive constructors (⊥, var, ∧, →, □), together
with their notation, simplification lemmas, and basic properties.

## Design

The five primitive constructors form a functionally complete set. All
other connectives are definitional abbreviations:

  ∼φ      :=  φ ⊃ ⊥           (negation)
  ⊤       :=  ⊥ ⊃ ⊥           (verum)
  φ ⋎ ψ  :=  ∼φ ⊃ ψ          (disjunction)
  φ ⇔ ψ  :=  (φ ⊃ ψ) ∧ (ψ ⊃ φ)  (biconditional)
  ◇φ     :=  ∼□∼φ             (possibility)
-/

import ModalLogic.Syntax.Formula

namespace BasicModal

open Form

------------------------------------------------------------------------------
-- § 1. Derived Operators
------------------------------------------------------------------------------

/-- **Negation**: ∼φ := φ ⊃ ⊥ -/
def neg (φ : Form) : Form :=
  Form.impl φ Form.bot

/-- **Verum**: ⊤ := ⊥ ⊃ ⊥ (a tautology serving as the constant true) -/
def top : Form :=
  neg Form.bot

/-- **Disjunction**: φ ⋎ ψ := ∼φ ⊃ ψ -/
def or (φ ψ : Form) : Form :=
  Form.impl (neg φ) ψ

/-- **Biconditional**: φ ⇔ ψ := (φ ⊃ ψ) ∧ (ψ ⊃ φ) -/
def iff (φ ψ : Form) : Form :=
  Form.and (Form.impl φ ψ) (Form.impl ψ φ)

/-- **Possibility**: ◇φ := ∼□∼φ -/
def dia (φ : Form) : Form :=
  neg (Form.box (neg φ))

------------------------------------------------------------------------------
-- § 2. Notation
--
-- Activate with `open Modal` (or `open BasicModal.Modal`).
-- Precedences follow classical convention: ∼ and □/◇ bind tightest,
-- then ∧ (&), then ∨ (⋎), then → (⊃), then ↔ (⇔).
------------------------------------------------------------------------------

namespace Modal

notation "⊥ₘ" => Form.bot
notation "⊤ₘ" => top

prefix:max "∼"  => neg
prefix:max "¬ₘ" => neg        -- alternative negation notation
prefix:75  "□ " => Form.box
prefix:75  "◇ " => dia

infixr:70  " & "  => Form.and
infixr:65  " ⋎ "  => or       -- modal disjunction (⋎ avoids shadowing Lean's ∨)
infixr:60  " ⊃ "  => Form.impl
infixr:60  " ⇔ "  => iff

end Modal

------------------------------------------------------------------------------
-- § 3. Definitional Simp Lemmas
------------------------------------------------------------------------------

@[simp] theorem neg_def  (φ : Form)   : neg φ   = Form.impl φ Form.bot                        := rfl
@[simp] theorem top_def               : top     = Form.impl Form.bot Form.bot                  := rfl
@[simp] theorem or_def   (φ ψ : Form) : or φ ψ  = Form.impl (neg φ) ψ                         := rfl
@[simp] theorem iff_def  (φ ψ : Form) : iff φ ψ = Form.and (Form.impl φ ψ) (Form.impl ψ φ)   := rfl
@[simp] theorem dia_def  (φ : Form)   : dia φ   = neg (Form.box (neg φ))                      := rfl

-- Useful unfolding: ⊤ is the same as ¬⊥
@[simp] theorem neg_bot : neg Form.bot = top := rfl

------------------------------------------------------------------------------
-- § 4. Complexity
------------------------------------------------------------------------------

/-- Negation adds one implication and one ⊥, so complexity increases by 2. -/
@[simp]
theorem complexity_neg (φ : Form) : complexity (neg φ) = 2 + complexity φ := by
  simp [neg, complexity]; omega

/-- Verum has complexity 3 (= impl bot bot = 1 + 1 + 1). -/
@[simp]
theorem complexity_top : complexity top = 3 := by
  simp [top, neg, complexity]

/-- Disjunction wraps two negations and an implication: 3 + cφ + cψ. -/
@[simp]
theorem complexity_or (φ ψ : Form) :
    complexity (or φ ψ) = 3 + complexity φ + complexity ψ := by
  simp [or, neg, complexity]; omega

/-- Biconditional is a conjunction of two implications: 3 + 2·cφ + 2·cψ. -/
@[simp]
theorem complexity_iff (φ ψ : Form) :
    complexity (iff φ ψ) = 3 + 2 * complexity φ + 2 * complexity ψ := by
  simp [iff, complexity]; omega

/-- Diamond wraps two negations and a box: 5 + cφ. -/
@[simp]
theorem complexity_dia (φ : Form) : complexity (dia φ) = 5 + complexity φ := by
  simp [dia, neg, complexity]; omega

------------------------------------------------------------------------------
-- § 5. Modal Depth
------------------------------------------------------------------------------

/-- Negation is a propositional connective: it does not change modal depth. -/
@[simp]
theorem modalDepth_neg (φ : Form) : modalDepth (neg φ) = modalDepth φ := by
  simp [neg, modalDepth]

/-- Verum contains no modalities. -/
@[simp]
theorem modalDepth_top : modalDepth top = 0 := by
  simp [top, neg, modalDepth]

/-- Modal depth of disjunction is the max of the two operands. -/
@[simp]
theorem modalDepth_or (φ ψ : Form) :
    modalDepth (or φ ψ) = max (modalDepth φ) (modalDepth ψ) := by
  simp [or, neg, modalDepth]

/-- Modal depth of biconditional is the max of the two operands. -/
@[simp]
theorem modalDepth_iff (φ ψ : Form) :
    modalDepth (iff φ ψ) = max (modalDepth φ) (modalDepth ψ) := by
  simp [iff, modalDepth, Nat.max_comm]

/-- Diamond increases modal depth by one (it contains □). -/
@[simp]
theorem modalDepth_dia (φ : Form) : modalDepth (dia φ) = 1 + modalDepth φ := by
  simp [dia, neg, modalDepth]

------------------------------------------------------------------------------
-- § 6. Variable Sets
------------------------------------------------------------------------------

/-- Negation does not introduce or remove variables. -/
@[simp]
theorem vars_neg (φ : Form) : vars (neg φ) = vars φ := by
  simp [neg, vars]

/-- Verum contains no propositional variables. -/
@[simp]
theorem vars_top : vars top = ∅ := by aesop

/-- Variables in a disjunction are the union of the operands' variables. -/
@[simp]
theorem vars_or (φ ψ : Form) : vars (or φ ψ) = vars φ ∪ vars ψ := by
  simp [or, neg, vars]

/-- Variables in a biconditional are the union of the operands' variables. -/
@[simp]
theorem vars_iff (φ ψ : Form) : vars (iff φ ψ) = vars φ ∪ vars ψ := by
  simp [iff, vars, Finset.union_comm (vars ψ) (vars φ)]

/-- Diamond does not introduce or remove variables. -/
@[simp]
theorem vars_dia (φ : Form) : vars (dia φ) = vars φ := by
  simp [dia, neg, vars]

------------------------------------------------------------------------------
-- § 7. Standard Modal Axiom Schemas
--
-- These are formula-level definitions of the well-known modal axiom schemas.
-- Their provability in the respective systems is established in ProofSystem.lean.
------------------------------------------------------------------------------

/-- Law of excluded middle: φ ⋎ ∼φ -/
def excludedMiddle (φ : Form) : Form :=
  or φ (neg φ)

/-- Law of non-contradiction: ∼(φ ∧ ∼φ) -/
def nonContradiction (φ : Form) : Form :=
  neg (Form.and φ (neg φ))

/-- **K axiom**: □(φ ⊃ ψ) ⊃ (□φ ⊃ □ψ) — the defining axiom of system K -/
def axiomK (φ ψ : Form) : Form :=
  Form.impl (Form.box (Form.impl φ ψ))
            (Form.impl (Form.box φ) (Form.box ψ))

/-- **T axiom**: □φ ⊃ φ — reflexivity axiom (K → T) -/
def axiomT (φ : Form) : Form :=
  Form.impl (Form.box φ) φ

/-- **4 axiom**: □φ ⊃ □□φ — transitivity axiom (K → K4 / S4) -/
def axiom4 (φ : Form) : Form :=
  Form.impl (Form.box φ) (Form.box (Form.box φ))

/-- **5 axiom**: ◇φ ⊃ □◇φ — Euclidean axiom (K → S5) -/
def axiom5 (φ : Form) : Form :=
  Form.impl (dia φ) (Form.box (dia φ))

/-- **B axiom**: φ ⊃ □◇φ — symmetry axiom (K → KB) -/
def axiomB (φ : Form) : Form :=
  Form.impl φ (Form.box (dia φ))

/-- **D axiom**: □φ ⊃ ◇φ — seriality axiom (K → KD) -/
def axiomD (φ : Form) : Form :=
  Form.impl (Form.box φ) (dia φ)

end BasicModal
