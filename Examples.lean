/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Examples for Modal Logic K

This file contains worked examples demonstrating the use of the modal logic formalization.

## Contents
1. Basic Formula Construction
2. Provable Theorems in K
3. Working with the Proof System
-/

import ModalLogic

namespace Modal.Examples

open BasicModal
open BasicModal.Modal  -- Open the nested namespace where notation is defined

------------------------------------------------------------------------------
-- § 1. Basic Formula Construction
------------------------------------------------------------------------------

/-- Propositional variable p -/
def myP : Form := Form.var 0

/-- Propositional variable q -/
def myQ : Form := Form.var 1

/-- Propositional variable r -/
def myR : Form := Form.var 2

/-- Example compound formula: □(p → q) -/
def box_impl : Form := Form.box (Form.impl myP myQ)

/-- Example compound formula: □p ∧ □q -/
def box_and_box : Form := Form.and (Form.box myP) (Form.box myQ)

/-- Example nested modality: □□p -/
def double_box : Form := Form.box (Form.box myP)

/-- Example using negation (derived): ¬p -/
def neg_p : Form := neg myP

/-- Example using disjunction (derived): p ∨ q -/
def p_or_q : Form := or myP myQ

/-- Example using diamond (derived): ◇p -/
def diamond_p : Form := dia myP

------------------------------------------------------------------------------
-- § 2. Provable Theorems in System K
------------------------------------------------------------------------------

/-- **Example 1**: The K axiom is provable -/
example : ∅ ⊢K (Form.impl (Form.box (Form.impl myP myQ))
                           (Form.impl (Form.box myP) (Form.box myQ))) :=
  ProofK.kdist

/-- **Example 2**: Propositional axiom PL1 -/
example : ∅ ⊢K (Form.impl myP (Form.impl myQ myP)) :=
  ProofK.pl1

/-- **Example 3**: Conjunction introduction -/
example : ∅ ⊢K (Form.impl myP (Form.impl myQ (Form.and myP myQ))) :=
  ProofK.pl4

/-- **Example 4**: Conjunction elimination (left) -/
example : ∅ ⊢K (Form.impl (Form.and myP myQ) myP) :=
  ProofK.pl5

/-- **Example 5**: Conjunction elimination (right) -/
example : ∅ ⊢K (Form.impl (Form.and myP myQ) myQ) :=
  ProofK.pl6

------------------------------------------------------------------------------
-- § 3. Using Modus Ponens and Necessitation
------------------------------------------------------------------------------

/-- **Example 6**: Modus ponens rule -/
example (h1 : ∅ ⊢K (Form.impl myP myQ)) (h2 : ∅ ⊢K myP) : ∅ ⊢K myQ :=
  ProofK.mp h1 h2

/-- **Example 7**: Necessitation rule -/
example (h : ∅ ⊢K myP) : ∅ ⊢K (Form.box myP) :=
  ProofK.nec h

/-- **Example 8**: Chaining necessitation and K axiom -/
example (h1 : ∅ ⊢K (Form.impl myP myQ)) (h2 : ∅ ⊢K (Form.box myP)) :
    ∅ ⊢K (Form.box myQ) := by
  -- Necessitate the implication
  have h3 : ∅ ⊢K (Form.box (Form.impl myP myQ)) := ProofK.nec h1
  -- Apply K axiom
  have k : ∅ ⊢K (Form.impl (Form.box (Form.impl myP myQ))
                            (Form.impl (Form.box myP) (Form.box myQ))) := ProofK.kdist
  -- Get □p → □q
  have h4 : ∅ ⊢K (Form.impl (Form.box myP) (Form.box myQ)) := ProofK.mp k h3
  -- Apply to □p
  exact ProofK.mp h4 h2

------------------------------------------------------------------------------
-- § 4. Formula Properties
------------------------------------------------------------------------------

/-- **Example 9**: Computing complexity -/
example : complexity myP = 1 := rfl

example : complexity (Form.impl myP myQ) = 3 := rfl

example : complexity (Form.box myP) = 2 := rfl

/-- **Example 10**: Computing modal depth -/
example : modalDepth myP = 0 := rfl

example : modalDepth (Form.box myP) = 1 := rfl

example : modalDepth (Form.box (Form.box myP)) = 2 := rfl

/-- **Example 11**: Extracting variables -/
example : vars myP = {0} := rfl

example : vars (Form.and myP myQ) = {0, 1} := by
  simp [vars]
  rfl

------------------------------------------------------------------------------
-- § 5. Working with Contexts
------------------------------------------------------------------------------

/-- **Example 12**: Using hypotheses -/
example (h : myP ∈ ({myP} : Ctx)) : {myP} ⊢K myP :=
  ProofK.hyp h

/-- **Example 13**: Proving from assumptions -/
example : {myP, Form.impl myP myQ} ⊢K myQ := by
  have h1 : {myP, Form.impl myP myQ} ⊢K (Form.impl myP myQ) :=
    ProofK.hyp (by simp)
  have h2 : {myP, Form.impl myP myQ} ⊢K myP :=
    ProofK.hyp (by simp)
  exact ProofK.mp h1 h2

------------------------------------------------------------------------------
-- § 6. Comments on Non-Theorems
------------------------------------------------------------------------------

/-!
## Non-Theorems of K

The following formulas are **NOT** provable in system K without additional axioms:

1. **T axiom**: □p → p
   - Requires reflexive frames
   - Not valid in all Kripke frames

2. **4 axiom**: □p → □□p
   - Requires transitive frames
   - Defines system K4

3. **5 axiom**: ◇p → □◇p
   - Requires Euclidean frames
   - Defines system K5/S5

4. **D axiom**: □p → ◇p
   - Requires serial frames (every world sees at least one world)
   - Defines system KD

These axioms can be added to extend K to stronger systems (T, S4, S5, etc.).
The project defines these axiom schemas in ProofSystem.lean.
-/

------------------------------------------------------------------------------
-- § 7. Using Derived Operators
------------------------------------------------------------------------------

/-- **Example 14**: Negation is defined as implication to falsity -/
example : neg myP = Form.impl myP Form.bot := rfl

/-- **Example 15**: Disjunction is defined using negation and implication -/
example : or myP myQ = Form.impl (neg myP) myQ := rfl

/-- **Example 16**: Diamond (possibility) is defined using box and negation -/
example : dia myP = neg (Form.box (neg myP)) := rfl

/-- **Example 17**: Complexity of derived operators -/
example : complexity (neg myP) = 3 := by
  simp [neg, complexity, myP]

example : complexity (dia myP) = 6 := by
  simp [dia, neg, complexity, myP]

end Modal.Examples
