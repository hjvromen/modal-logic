/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Experimental Proof Infrastructure

**Status**: This file is **experimental** and not part of the main development.
None of its definitions are imported by other files in the library. It is
preserved as a sandbox for future extensions and may be freely modified or
removed without affecting the core results.

## Contents

- **`DerivK`**: Type-valued derivation trees (vs. `ProofK` which lives in `Prop`),
  enabling recursive functions on proofs such as `proofDepth` and `proofSize`.
- **`isPropAxiom` / `isKAxiom`**: Computable recognizers for axiom schemas,
  useful for proof search or a future tableau/decision procedure.
- **`cutFree`**: A structural predicate on derivation trees. Trivially true
  for Hilbert systems, but provided as a hook for future proof-tree analysis.
- **`deducibleFrom`**: Deducibility from a finite list of assumptions.

## Potential Future Uses

- **Proof search / tableau method**: `isPropAxiom` and `isKAxiom` could drive
  a computable proof checker or decision procedure.
- **Proof normalization**: `DerivK` enables induction on proof structure for
  normalization and subformula property results.
- **Decidability of K**: proof size bounds via `proofDepth` / `proofSize`
  could contribute to a decidability argument.
-/

import ModalLogic.Syntax.ProofSystem

namespace BasicModal

open Modal

------------------------------------------------------------------------------
-- § 1. Type-Valued Derivation Trees
------------------------------------------------------------------------------

/--
`DerivK` represents explicit derivation trees in the Hilbert-style
modal logic **K**.  It is structurally identical to `ProofK`, but lives
in `Type` instead of `Prop`, allowing us to define recursive
functions like `proofSize`.
-/
inductive DerivK : Ctx → Form → Type where
  | hyp  {Γ φ} (h : φ ∈ Γ) : DerivK Γ φ
  | pl1  {Γ φ ψ} : DerivK Γ (φ ⊃ (ψ ⊃ φ))
  | pl2  {Γ φ ψ χ} :
      DerivK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
  | pl3  {Γ φ ψ} :
      DerivK Γ (((¬ₘφ) ⊃ (¬ₘψ)) ⊃ (ψ ⊃ φ))
  | pl4  {Γ φ ψ} : DerivK Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
  | pl5  {Γ φ ψ} : DerivK Γ ((φ & ψ) ⊃ φ)
  | pl6  {Γ φ ψ} : DerivK Γ ((φ & ψ) ⊃ ψ)
  | kdist {Γ φ ψ} :
      DerivK Γ ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))
  | mp  {Γ φ ψ} (hpq : DerivK Γ (φ ⊃ ψ)) (hp : DerivK Γ φ) :
      DerivK Γ ψ
  | nec {Γ φ} (hp : DerivK Γ φ) :
      DerivK Γ (□ φ)

theorem DerivK_sound {Γ φ} (d : DerivK Γ φ) : ProofK Γ φ := by
  induction d with
  | hyp hφ         => exact ProofK.hyp hφ
  | pl1            => exact ProofK.pl1
  | pl2            => exact ProofK.pl2
  | pl3            => exact ProofK.pl3
  | pl4            => exact ProofK.pl4
  | pl5            => exact ProofK.pl5
  | pl6            => exact ProofK.pl6
  | kdist          => exact ProofK.kdist
  | mp _ _ ih₁ ih₂ => exact ProofK.mp ih₁ ih₂
  | nec _ ih       => exact ProofK.nec ih

------------------------------------------------------------------------------
-- § 2. Computable Axiom Recognizers
------------------------------------------------------------------------------

/--
Check if a formula matches one of the PL1–PL6 propositional axiom schemas.

This is computable: `DecidableEq Form` (derived via `deriving`) makes
all equality tests decidable.
-/
def isPropAxiom : Form → Bool
  -- K first (unique □-shape)
  | Form.impl
      (Form.box (Form.impl φ ψ))
      (Form.impl (Form.box φ') (Form.box ψ')) =>
      decide (φ = φ' ∧ ψ = ψ')

  -- All other axioms (PL1–PL6)
  | Form.impl a b =>
    match a, b with
    | Form.impl φ (Form.impl ψ₁ χ₁),
      Form.impl (Form.impl φ' ψ₂) (Form.impl φ'' χ₂) =>
        decide (φ = φ' ∧ φ = φ'' ∧ ψ₁ = ψ₂ ∧ χ₁ = χ₂)
    | Form.impl (Form.impl φ₁ Form.bot) (Form.impl ψ₁ Form.bot),
      Form.impl (Form.impl (Form.impl φ₂ Form.bot) ψ₂) φ₃ =>
        decide (φ₁ = φ₂ ∧ φ₁ = φ₃ ∧ ψ₁ = ψ₂)
    | φ, Form.impl ψ (Form.and φ' ψ') =>
        decide (φ = φ' ∧ ψ = ψ')
    | Form.and φ ψ, χ =>
        decide ((χ = φ) ∨ (χ = ψ))
    | Form.impl (Form.impl φ₁ Form.bot) (Form.impl ψ₁ Form.bot),
      Form.impl ψ₂ φ₂ =>
        decide (φ₁ = φ₂ ∧ ψ₁ = ψ₂)
    | φ, Form.impl _ χ =>
        decide (χ = φ)
    | _, _ => false

  | _ => false


/--
Check if a formula is an instance of the K axiom schema □(φ→ψ)→(□φ→□ψ).

Verifies that the inner formulas φ and ψ match up correctly.
-/
def isKAxiom : Form → Bool
  | Form.impl (Form.box (Form.impl φ ψ))
              (Form.impl (Form.box φ') (Form.box ψ')) =>
      decide (φ = φ' ∧ ψ = ψ')
  | _ => false

------------------------------------------------------------------------------
-- § 3. Proof Depth and Complexity
------------------------------------------------------------------------------

/--
**Proof depth**: length of the longest branch in a derivation tree.

Measures how many inference steps are needed.

**Properties**:
- Hypothesis: depth 1
- Axioms: depth 1
- Modus ponens: max(depth of premises) + 1
- Necessitation: depth of premise + 1

**Applications**:
- Complexity analysis
- Proof search bounds
- Normalization theorems
-/
def proofDepth {Γ φ} : DerivK Γ φ → Nat
  | DerivK.hyp _ => 1
  | DerivK.pl1 | DerivK.pl2 | DerivK.pl3 | DerivK.pl4
  | DerivK.pl5 | DerivK.pl6 | DerivK.kdist => 1
  | DerivK.mp hpq hp => 1 + Nat.max (proofDepth hpq) (proofDepth hp)
  | DerivK.nec hp => 1 + proofDepth hp


/--
**Proof size**: total number of nodes in the derivation tree.

Counts all formulas used in the proof.

**Properties**:
- Always ≥ proof depth
- Measures total proof "work"
- Relevant for proof compression
-/
def proofSize {Γ : Ctx} {φ : Form} : DerivK Γ φ → Nat
  | DerivK.hyp _ | DerivK.pl1 | DerivK.pl2 | DerivK.pl3 | DerivK.pl4
  | DerivK.pl5   | DerivK.pl6 | DerivK.kdist => 1
  | DerivK.mp hpq hp => 1 + proofSize hpq + proofSize hp
  | DerivK.nec hp    => 1 + proofSize hp


/--
Proof size is at least the depth.
-/
theorem proofDepth_le_proofSize {Γ φ} (h : DerivK Γ φ) :
    proofDepth h ≤ proofSize h := by
  induction h with
  | hyp _ =>
      simp [proofDepth, proofSize]
  | pl1 | pl2 | pl3 | pl4 | pl5 | pl6 | kdist =>
      simp [proofDepth, proofSize]
  | mp hpq hp ih₁ ih₂ =>
      simp [proofDepth, proofSize]
      rw [Nat.add_assoc]
      apply Nat.add_le_add_left
      exact (Nat.max_le).mpr
        ⟨le_trans (b := proofSize hpq) (c := proofSize hpq + proofSize hp)
            ih₁ (Nat.le_add_right _ _),
         le_trans (b := proofSize hp) (c := proofSize hpq + proofSize hp)
            ih₂ (Nat.le_add_left _ _)⟩
  | nec hp ih =>
      simp [proofDepth, proofSize]
      exact ih

------------------------------------------------------------------------------
-- § 4. Normal Forms for Proofs
------------------------------------------------------------------------------

/--
**Structural predicate on derivation trees**.

`cutFree d` holds for every derivation `d : DerivK Γ φ`. In a Hilbert
system, modus ponens cannot be eliminated — every non-trivial derivation
uses it — so "cut-free" in the sequent-calculus sense is not meaningful here.
This predicate is provided as a structural hook for future extension
(e.g., tracking specific proof-tree properties).

See `all_proofs_cutfree` for the trivial proof that it always holds.
-/
def cutFree {Γ : Ctx} {φ : Form} : DerivK Γ φ → Prop
  | DerivK.hyp _      => True
  | DerivK.pl1        => True
  | DerivK.pl2        => True
  | DerivK.pl3        => True
  | DerivK.pl4        => True
  | DerivK.pl5        => True
  | DerivK.pl6        => True
  | DerivK.kdist      => True
  | DerivK.mp d₁ d₂   => cutFree d₁ ∧ cutFree d₂
  | DerivK.nec d      => cutFree d

/--
Every proof is "cut-free" in the trivial sense for Hilbert systems.
-/
theorem all_proofs_cutfree {Γ φ} (d : DerivK Γ φ) : cutFree d := by
  induction d with
  | hyp _ => trivial
  | pl1 | pl2 | pl3 | pl4 | pl5 | pl6 | kdist => trivial
  | mp _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | nec _ ih => exact ih

------------------------------------------------------------------------------
-- § 5. Finite Deducibility
------------------------------------------------------------------------------

/--
**Deducible**: φ is deducible from a finite list of assumptions.

Useful for constructive proofs and algorithms.
-/
def deducibleFrom (L : List Form) (φ : Form) : Prop :=
  ∅ ⊢K (L.foldr (λ ψ χ => ψ ⊃ χ) φ)

end BasicModal
