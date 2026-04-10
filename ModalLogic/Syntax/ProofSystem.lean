/-
Copyright (c) 2025 Huub Vromen.
Improved and modularized version

# Hilbert-Style Proof System K

This file establishes the proof system for modal propositional logic K,
the minimal normal modal logic.

## The System K

**K is the minimal normal modal logic**, containing:
- All classical propositional tautologies (PL1-PL6)
- The K axiom: □(φ → ψ) → (□φ → □ψ) (distribution of necessity)
- Modus ponens: from φ and φ → ψ, derive ψ
- Necessitation: from φ, derive □φ

**Why "K"?** Named after Saul Kripke, who established the semantic foundations.

**Normality**: K is the basic "normal" modal logic. A modal logic is normal if:
1. It contains all propositional tautologies
2. It has the K axiom
3. It's closed under modus ponens and necessitation

All standard modal logics (T, S4, S5, etc.) extend K by adding axioms.
-/

import ModalLogic.Syntax.Derived

namespace BasicModal

open Modal

------------------------------------------------------------------------------
-- § 1. Contexts (Sets of Formulas)
------------------------------------------------------------------------------

/--
**Context**: A set of formula assumptions.

Contexts represent collections of assumptions or axioms.
We use Mathlib's `Set` type for maximum flexibility.

**Operations**:
- `∅`: Empty context (no assumptions)
- `{φ}`: Singleton context
- `Γ ∪ {φ}`: Insert φ into Γ
- `Γ ∪ Δ`: Union of contexts
- `φ ∈ Γ`: Membership test

**Usage**:
- Axiom systems (e.g., TAxioms = {□φ → φ | φ : form})
- Proof contexts (assumptions available for derivation)
- Theories (closed under consequence)
-/
abbrev Ctx : Type := Set Form

/--
**Context insertion notation**: Γ ∪ₛ φ means Γ ∪ {φ}.

We use ∪ₛ instead of ∪ to avoid confusion with set union
and to make single-element insertion explicit.

**Example**:
```lean
let Γ : Ctx := {p, q}
let Γ' := Γ ∪ₛ r  -- {p, q, r}
```
-/
notation:50 Γ:50 " ∪ₛ " φ:50 => Γ ∪ {φ}

------------------------------------------------------------------------------
-- § 2. The Proof System ProofK
------------------------------------------------------------------------------

/--
**Derivability in system K**: The relation `ProofK Γ φ` means φ is derivable
from assumptions Γ using the K proof system.

This inductive type defines when a formula is provable. Each constructor
represents either an axiom or an inference rule.

## Axioms

**Propositional Axioms** (PL1-PL6): Sufficient for all classical propositional logic
- PL1 (K combinator): φ → (ψ → φ)
- PL2 (S combinator): (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
- PL3 (contraposition): ((¬φ → ¬ψ) → (ψ → φ))
- PL4 (conjunction intro): φ → (ψ → (φ ∧ ψ))
- PL5 (conjunction elim left): (φ ∧ ψ) → φ
- PL6 (conjunction elim right): (φ ∧ ψ) → ψ

**Modal Axiom**:
- K (distribution): □(φ → ψ) → (□φ → □ψ)

## Inference Rules

- **Hypothesis** (hyp): If φ ∈ Γ, then Γ ⊢ φ
- **Modus Ponens** (mp): From Γ ⊢ (φ → ψ) and Γ ⊢ φ, derive Γ ⊢ ψ
- **Necessitation** (nec): From Γ ⊢ φ, derive Γ ⊢ □φ

## Design Choices

**Why Hilbert-style?**
- Minimalist: few axioms and rules
- Uniform: same structure for all normal modal logics
- Historic: classical approach to modal logic
- Proof-theoretic: natural for metamathematical results

**Trade-offs**:
- Proofs are longer (but we derive helper lemmas)
- Less intuitive than natural deduction
- Perfect for metatheory (soundness, completeness, decidability)

**Note on Necessitation**: This rule only applies to full derivations,
not to mere assumptions! If φ ∈ Γ, we do NOT generally have □φ ∈ Γ.
-/
inductive ProofK : Ctx → Form → Prop where

  /-- **Hypothesis rule**: Assumptions can be used in derivations -/
  | hyp {Γ φ} (h : φ ∈ Γ) : ProofK Γ φ

  /-- **Axiom PL1** (K combinator): Weakening - we can always ignore premises -/
  | pl1 {Γ φ ψ} :
      ProofK Γ (φ ⊃ (ψ ⊃ φ))

  /-- **Axiom PL2** (S combinator): Distribution of implication -/
  | pl2 {Γ φ ψ χ} :
      ProofK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))

  /-- **Axiom PL3**: Contraposition -/
  | pl3 {Γ φ ψ} :
      ProofK Γ (((¬ₘφ) ⊃ (¬ₘψ)) ⊃ (ψ ⊃ φ))

  /-- **Axiom PL4**: Conjunction introduction (uncurried) -/
  | pl4 {Γ φ ψ} :
      ProofK Γ (φ ⊃ (ψ ⊃ (φ & ψ)))

  /-- **Axiom PL5**: Left conjunction elimination (first projection) -/
  | pl5 {Γ φ ψ} :
      ProofK Γ ((φ & ψ) ⊃ φ)

  /-- **Axiom PL6**: Right conjunction elimination (second projection) -/
  | pl6 {Γ φ ψ} :
      ProofK Γ ((φ & ψ) ⊃ ψ)

  /-- **K axiom**: Distribution of necessity over implication.
      This is THE characteristic axiom of normal modal logic.
      Semantically valid in ALL Kripke frames. -/
  | kdist {Γ φ ψ} :
      ProofK Γ ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))

  /-- **Modus ponens**: The fundamental inference rule.
      From φ and φ→ψ, conclude ψ.
      This is how we actually DO reasoning. -/
  | mp {Γ φ ψ}
      (hpq : ProofK Γ (φ ⊃ ψ))
      (hp  : ProofK Γ φ) :
      ProofK Γ ψ

  /-- **Necessitation**: Theorems are necessarily true.
      If φ is derivable, then □φ is derivable.
      This makes K a "normal" modal logic.

      **Crucial**: Only applies to full derivations, not mere assumptions!

      **Design Note on Unrestricted Necessitation**: This rule applies to
      derivations from *any* context Γ, not just the empty context. This means
      `{p} ⊢K □p` is derivable (necessitate the hypothesis). This is sound
      under our **global semantic consequence** (`globalSemCsq`), where hypotheses
      are assumed to hold at *every* world in the model — so if `p` holds everywhere,
      `□p` trivially holds everywhere too.

      However, this would NOT be sound under **local (pointwise) consequence**
      (`localSemCsq`, defined in `LocalConsequence.lean`), where hypotheses hold
      only at the evaluation world. Under local consequence, `p` true at world `w`
      does not imply `□p` at `w`, because `p` may fail at accessible worlds.

      See `LocalConsequence.lean` for the formal proof of this gap
      (`local_global_gap`), and for a necessitation-free proof system (`ProofK_noNec`)
      that IS sound for local consequence. -/
  | nec {Γ φ}
      (hp  : ProofK Γ φ) :
      ProofK Γ (□ φ)

/--
**Turnstile notation**: Γ ⊢K φ means "φ is derivable from Γ in system K".

This is standard proof-theoretic notation:
- The turnstile ⊢ separates assumptions (left) from conclusion (right)
- The subscript K specifies which proof system

**Reading**: "Gamma proves phi in K" or "phi is K-derivable from Gamma"

**Special cases**:
- `∅ ⊢K φ`: φ is a theorem of K (provable without assumptions)
- `Γ ⊢K ⊥ₘ`: Γ is inconsistent (derives contradiction)
- `Γ ⊢K (φ ⊃ ψ)`: ψ is a consequence of φ relative to Γ
-/
notation:50 Γ " ⊢K " φ:50 => ProofK Γ φ

------------------------------------------------------------------------------
-- § 3. Standard Axiom Systems
------------------------------------------------------------------------------

/--
**T axioms**: Reflexivity axioms for logic T.

T extends K with the axiom schema: □φ → φ (necessity implies truth)

This is valid in reflexive frames (where every world sees itself).
-/
def TAxioms : Ctx := { φ | ∃ ψ, φ = □ ψ ⊃ ψ }

/--
**S4 axioms**: T + transitivity axiom.

S4 extends T with: □φ → □□φ (what's necessary is necessarily necessary)

Valid in reflexive and transitive frames.
-/
def S4Axioms : Ctx := TAxioms ∪ { φ | ∃ ψ, φ = □ ψ ⊃ □ (□ ψ) }

/--
**S5 axioms**: T + Euclidean/symmetric axiom.

S5 extends T with: ◇φ → □◇φ (what's possible is necessarily possible)

Valid in equivalence relation frames (reflexive, symmetric, transitive).
-/
def S5Axioms : Ctx := TAxioms ∪ { φ | ∃ ψ, φ = ◇ ψ ⊃ □ (◇ ψ) }

/--
**KD axioms**: K + seriality (D axiom).

KD extends K with: □φ → ◇φ (necessity implies possibility)

Valid in serial frames (every world sees at least one world).
Used in deontic logic.
-/
def KDAxioms : Ctx := { φ | ∃ ψ, φ = □ ψ ⊃ ◇ ψ }

/--
**KB axioms**: K + symmetry (B axiom).

KB extends K with: φ → □◇φ (truth implies necessary possibility)

Valid in symmetric frames.
-/
def KBAxioms : Ctx := { φ | ∃ ψ, φ = ψ ⊃ □ (◇ ψ) }

/--
**K4 axioms**: K + transitivity.

K4 extends K with: □φ → □□φ

Valid in transitive frames (not necessarily reflexive).
-/
def K4Axioms : Ctx := { φ | ∃ ψ, φ = □ ψ ⊃ □ (□ ψ) }

/--
**KTB axioms**: K + reflexivity + symmetry (Brouwerian logic).

KTB extends K with:
- T axiom: □φ → φ (reflexivity)
- B axiom: φ → □◇φ (symmetry)

Valid in reflexive and symmetric frames.
-/
def KTBAxioms : Ctx := TAxioms ∪ KBAxioms

/--
**KB4 axioms**: K + symmetry + transitivity.

KB4 extends K with:
- B axiom: φ → □◇φ (symmetry)
- 4 axiom: □φ → □□φ (transitivity)

Valid in symmetric and transitive frames.
-/
def KB4Axioms : Ctx := KBAxioms ∪ K4Axioms

/--
**K5 axioms**: K + Euclidean property (5 axiom).

K5 extends K with: ◇φ → □◇φ (what's possible is necessarily possible)

Valid in Euclidean frames.

**Note**: S5 = T + 5, i.e., S5Axioms = TAxioms ∪ K5Axioms.
The 5 axiom alone (without reflexivity) gives a weaker logic.
-/
def K5Axioms : Ctx := { φ | ∃ ψ, φ = ◇ ψ ⊃ □ (◇ ψ) }

/--
**KD5 axioms**: K + seriality + Euclidean property.

KD5 extends K with:
- D axiom: □φ → ◇φ (seriality)
- 5 axiom: ◇φ → □◇φ (Euclidean)

Valid in serial Euclidean frames.
-/
def KD5Axioms : Ctx := KDAxioms ∪ K5Axioms

/--
**KD45 axioms**: K + seriality + transitivity + Euclidean property.

KD45 extends K with:
- D axiom: □φ → ◇φ (seriality)
- 4 axiom: □φ → □□φ (transitivity)
- 5 axiom: ◇φ → □◇φ (Euclidean)

Valid in serial, transitive, Euclidean frames.
Used in deontic logic with full introspection.
-/
def KD45Axioms : Ctx := KDAxioms ∪ K4Axioms ∪ K5Axioms

/--
**KDB axioms**: K + seriality + symmetry.

KDB extends K with:
- D axiom: □φ → ◇φ (seriality)
- B axiom: φ → □◇φ (symmetry)

Valid in serial symmetric frames.
-/
def KDBAxioms : Ctx := KDAxioms ∪ KBAxioms

/--
**KD4 axioms**: K + seriality + transitivity.

KD4 extends K with:
- D axiom: □φ → ◇φ (seriality)
- 4 axiom: □φ → □□φ (transitivity)

Valid in serial transitive frames.
-/
def KD4Axioms : Ctx := KDAxioms ∪ K4Axioms

/--
**K45 axioms**: K + transitivity + Euclidean property.

K45 extends K with:
- 4 axiom: □φ → □□φ (transitivity)
- 5 axiom: ◇φ → □◇φ (Euclidean)

Valid in transitive Euclidean frames.
-/
def K45Axioms : Ctx := K4Axioms ∪ K5Axioms

/--
**KB5 axioms**: K + symmetry + Euclidean property.

KB5 extends K with:
- B axiom: φ → □◇φ (symmetry)
- 5 axiom: ◇φ → □◇φ (Euclidean)

Valid in symmetric Euclidean frames. Since symmetric + Euclidean
implies transitive, KB5 = KB45.
-/
def KB5Axioms : Ctx := KBAxioms ∪ K5Axioms

------------------------------------------------------------------------------
-- § 4. Provability Predicates
------------------------------------------------------------------------------

/--
**Theorem**: A formula provable from empty context.

`Thm φ` means ∅ ⊢K φ, i.e., φ is provable without assumptions.
-/
def Thm (φ : Form) : Prop := ∅ ⊢K φ

/--
**Consistent context**: A context that doesn't prove falsity.

A context Γ is consistent if it doesn't derive contradiction.
-/
def consistent (Γ : Ctx) : Prop := ¬(Γ ⊢K ⊥ₘ)

/--
**Consequence**: φ is a consequence of Γ.

Just a readable alias for the turnstile notation.
-/
def consequence (Γ : Ctx) (φ : Form) : Prop := Γ ⊢K φ

end BasicModal
