/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Local Semantic Consequence

This file defines **local (pointwise) semantic consequence** and contrasts it with
the existing **global semantic consequence** from `Semantics.lean`.

## Motivation

The necessitation rule in our proof system `ProofK` applies to derivations from *any*
context: from `Γ ⊢K φ` we derive `Γ ⊢K □φ`. This makes derivations like
`{p} ⊢K □p` valid. Under the **global** semantic consequence (where all axioms hold
at *every* world), this is sound — the soundness theorem confirms it.

However, the standard textbook convention uses **local** (pointwise) consequence,
where `Γ ⊨_local φ` means: in every model and at every world where all formulas
in Γ are true *at that world*, φ is also true *at that world*. Under local
consequence, `{p} ⊨_local □p` fails: `p` can be true at one world without being
true at all accessible worlds.

## Key Results

1. **Local implies global**: `localSemCsq Γ φ → globalSemCsq Γ φ`
   (local consequence is *stronger* than global consequence)
2. **The converse fails**: `globalSemCsq {p} (□p)` but `¬ localSemCsq {p} (□p)`
3. **Local soundness for nec-free proofs**: The proof system without the
   unrestricted necessitation rule is sound for local consequence
4. **For ∅, the two notions coincide**: `localSemCsq ∅ φ ↔ globalSemCsq ∅ φ`

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §1.3 and §4.1
- Hughes & Cresswell, *A New Introduction to Modal Logic*, Ch. 1
-/

import ModalLogic.Semantics.Soundness

namespace Modal
open Modal
open BasicModal

/-!
## § 1. Local Semantic Consequence
-/

/--
**Local (pointwise) semantic consequence**: `Γ ⊨_local φ` means that in every
frame `F`, valuation `v`, and world `w`, if all formulas in `Γ` are true at `w`,
then `φ` is true at `w`.

This contrasts with `globalSemCsq` where the hypotheses must hold at *all* worlds
in the model simultaneously. The local version only requires hypotheses at the
*evaluation world*.

Local consequence is **stronger** than global consequence: `localSemCsq Γ φ`
implies `globalSemCsq Γ φ`, but not vice versa.

**Standard textbook notion**: Most modal logic textbooks use local consequence
as their primary semantic entailment relation.
-/
def localSemCsq (Γ : Ctx) (φ : Form) : Prop :=
  ∀ (F : Frame.{0}) v w, (∀ ψ ∈ Γ, forces F v w ψ) → forces F v w φ

/-!
## § 2. Relationship Between Global and Local Consequence
-/

/-- Local consequence implies global consequence. The converse does NOT hold
in general (see `local_global_gap`). -/
theorem localSemCsq_implies_globalSemCsq {Γ : Ctx} {φ : Form}
    (h : localSemCsq Γ φ) : globalSemCsq Γ φ := by
  exact fun F v hv x => h F v x fun ψ hψ => hv ψ x hψ

/-- For the empty context, global and local consequence coincide (both reduce
to universal validity). -/
theorem localSemCsq_empty_iff_globalSemCsq_empty {φ : Form} :
    localSemCsq ∅ φ ↔ globalSemCsq ∅ φ := by
  unfold localSemCsq globalSemCsq;
  unfold forcesCtx; aesop;

/-!
## § 3. The Gap: Counterexample Separating Local from Global Consequence

We show `{p₀} ⊨_global □p₀` (global consequence holds because `p₀` is forced
at every world by hypothesis) but `{p₀} ⊭_local □p₀` (local consequence fails
because `p₀` can hold at one world without holding at all accessible worlds).

This concretely demonstrates why the unrestricted necessitation rule is sound
for global consequence but would NOT be sound for local consequence.
-/

/-- `{var 0} ⊨_global □(var 0)`: under global consequence, if `var 0` holds at
every world, then `□(var 0)` holds everywhere. -/
theorem global_nec_example : globalSemCsq {Form.var 0} (Form.box (Form.var 0)) := by
  intro F v hv x; specialize hv ( p[0] ) ; aesop;

/-- `{var 0} ⊭_local □(var 0)`: countermodel is a two-world frame where
`var 0` holds at world 0 but not at accessible world 1. -/
theorem local_nec_counterexample : ¬ localSemCsq {Form.var 0} (Form.box (Form.var 0)) := by
  unfold localSemCsq;
  push_neg;
  -- Consider a two-world frame with states {0, 1} and relation R where 0 R 1.
  use ⟨Bool, fun x y => x = false ∧ y = true⟩;
  use fun n x => if n = 0 ∧ x = false then true else false; simp +decide [ forces ] ;

/--
**The gap theorem**: Global and local consequence do NOT coincide in general.
There exist `Γ` and `φ` such that `Γ ⊨_global φ` but `Γ ⊭_local φ`.

This concretely demonstrates the design choice in `ProofK.nec`:
our unrestricted necessitation rule is sound for global consequence but would
not be sound for local consequence.
-/
theorem local_global_gap :
    ∃ (Γ : Ctx) (φ : Form), globalSemCsq Γ φ ∧ ¬ localSemCsq Γ φ := by
  exact ⟨{Form.var 0}, Form.box (Form.var 0), global_nec_example, local_nec_counterexample⟩

/-!
## § 4. Local Soundness for Necessitation-Free Derivations

We define an inductive proof system without the necessitation rule (`ProofK_noNec`)
and show it is sound with respect to local consequence.
-/

/--
**Necessitation-free proof system**: The K proof system without the necessitation rule.

This system has the same axioms and modus ponens as `ProofK`, but omits the
necessitation rule. Derivations in this system are sound for local consequence.

**Note**: The K distribution axiom `□(φ → ψ) → (□φ → □ψ)` is still present
as a propositional axiom schema; what's removed is the *inference rule*
that promotes `⊢ φ` to `⊢ □φ`.
-/
inductive ProofK_noNec : Ctx → Form → Prop where
  | hyp {Γ φ} (h : φ ∈ Γ) : ProofK_noNec Γ φ
  | pl1 {Γ φ ψ} : ProofK_noNec Γ (φ ⊃ (ψ ⊃ φ))
  | pl2 {Γ φ ψ χ} : ProofK_noNec Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
  | pl3 {Γ φ ψ} : ProofK_noNec Γ (((¬ₘφ) ⊃ (¬ₘψ)) ⊃ (ψ ⊃ φ))
  | pl4 {Γ φ ψ} : ProofK_noNec Γ (φ ⊃ (ψ ⊃ (φ & ψ)))
  | pl5 {Γ φ ψ} : ProofK_noNec Γ ((φ & ψ) ⊃ φ)
  | pl6 {Γ φ ψ} : ProofK_noNec Γ ((φ & ψ) ⊃ ψ)
  | kdist {Γ φ ψ} : ProofK_noNec Γ ((□ (φ ⊃ ψ)) ⊃ ((□ φ) ⊃ (□ ψ)))
  | mp {Γ φ ψ} (hpq : ProofK_noNec Γ (φ ⊃ ψ)) (hp : ProofK_noNec Γ φ) : ProofK_noNec Γ ψ

/-- **Local soundness for the necessitation-free system**: Every formula derivable
without necessitation is a local semantic consequence. By induction on the
derivation—each axiom is locally valid, and modus ponens preserves local validity. -/
theorem local_soundness {Γ : Ctx} {φ : Form}
    (h : ProofK_noNec Γ φ) : localSemCsq Γ φ := by
  -- We proceed by induction on the structure of the proof `h`.
  induction' h with Γ φ ψ hpq hp hpq hp h_ind;
  all_goals unfold localSemCsq; aesop;

/--
**Global soundness implies derivability in the full system still gives global consequence**:
This is just a restatement confirming that our existing `soundness` theorem
is about global consequence.
-/
theorem global_soundness_restated {Γ : Ctx} {φ : Form}
    (h : ProofK Γ φ) : globalSemCsq Γ φ :=
  soundness Γ φ h

end Modal