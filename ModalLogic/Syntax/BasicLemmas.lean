/-
Copyright (c) 2025 Huub Vromen.
Improved and modularized version.

# Basic Structural Lemmas

This file establishes the fundamental structural properties of the proof system,
including weakening, contraction, and basic derived rules.

These are the "meta-rules" that govern how proofs behave with respect to contexts.
-/

import ModalLogic.Syntax.ProofSystem

namespace BasicModal

open Modal
open ProofK

variable {Γ Δ Θ : Ctx} {φ ψ χ : Form}

------------------------------------------------------------------------------
-- § 1. Structural Rules
------------------------------------------------------------------------------

namespace ProofK

/--
**Weakening (Monotonicity)**: Derivability is monotone with respect to contexts.

If Γ ⊢ φ and Γ ⊆ Δ, then Δ ⊢ φ.

**Proof strategy**: Induction on the derivation of φ from Γ.
- Hypothesis case: If φ ∈ Γ and Γ ⊆ Δ, then φ ∈ Δ
- Axiom cases: Axioms don't depend on context
- Rule cases: Apply induction hypothesis to premises

**Significance**: This is one of the fundamental **structural rules** of logic.
It says: adding more assumptions doesn't make things unprovable.

**Usage**: Essential for:
- Working with different contexts
- Proof by cases (extend context in each case)
- Modular reasoning (combine results from different contexts)

**Philosophical meaning**: Having more information/assumptions can't hurt.
This reflects the **monotonicity of knowledge**.
-/
theorem weakening (hsub : ∀ ⦃a⦄, a ∈ Γ → a ∈ Δ) :
    (Γ ⊢K φ) → (Δ ⊢K φ) := by
  intro h
  induction h with
  | hyp hmem         => exact ProofK.hyp (hsub hmem)
  | pl1              => exact ProofK.pl1
  | pl2              => exact ProofK.pl2
  | pl3              => exact ProofK.pl3
  | pl4              => exact ProofK.pl4
  | pl5              => exact ProofK.pl5
  | pl6              => exact ProofK.pl6
  | kdist            => exact ProofK.kdist
  | mp hpq hp ih_hpq ih_hp => exact ProofK.mp ih_hpq ih_hp
  | nec hp ih_hp     => exact ProofK.nec ih_hp

/--
**Weakening is idempotent**: Applying weakening twice is the same as once.
-/
theorem weakening_weakening (h1 : ∀ ⦃a⦄, a ∈ Γ → a ∈ Δ)
    (h2 : ∀ ⦃a⦄, a ∈ Δ → a ∈ Θ) (h : Γ ⊢K φ) :
    weakening h2 (weakening h1 h) = weakening (λ _ ha => h2 (h1 ha)) h := by
  induction h <;> rfl

/--
**Weakening is functorial**: Composing inclusions composes weakenings.
-/
theorem weakening_comp (h1 : ∀ ⦃a⦄, a ∈ Γ → a ∈ Δ)
    (h2 : ∀ ⦃a⦄, a ∈ Δ → a ∈ Θ) (h : Γ ⊢K φ) :
    weakening (λ _ ha => h2 (h1 ha)) h = weakening h2 (weakening h1 h) := by aesop

/--
**Hypothesis usage**: Any assumption in the context is derivable.

Trivial but fundamental: if φ ∈ Γ, then Γ ⊢ φ.

This is just the hypothesis rule as a theorem rather than constructor.
-/
@[simp] theorem of_mem (h : φ ∈ Γ) : Γ ⊢K φ := ProofK.hyp h

/--
**Insertion usage**: An inserted formula is immediately derivable.

If we add φ to the context, we can derive φ.

Trivial but used constantly: the inserted formula becomes an available hypothesis.
-/
@[simp] theorem of_insert : (Γ ∪ₛ φ) ⊢K φ := by
  apply ProofK.hyp
  simp

/--
**Weakening by insertion**: Special case of weakening.

If Γ ⊢ φ, then (Γ ∪ {ψ}) ⊢ φ.

**Usage**: The most common form of weakening - adding a single extra hypothesis.
Used in:
- Proof by cases
- Temporary assumptions
- Deduction steps
-/
theorem weaken_insert_right (h : Γ ⊢K φ) : (Γ ∪ₛ ψ) ⊢K φ :=
  weakening (by intro a ha; simpa [Set.insert] using Or.inr ha) h

/--
**Weakening by insertion (left)**: Symmetric version.
-/
theorem weaken_insert_left (h : Γ ⊢K φ) : ({ψ} ∪ Γ) ⊢K φ :=
  weakening (by intro a ha; simp; right; exact ha) h

/--
**Union weakening (left)**: Weaken from left component of union.
-/
theorem weaken_union_left (h : Γ ⊢K φ) : (Γ ∪ Δ) ⊢K φ :=
  weakening (by intro a ha; exact Or.inl ha) h

/--
**Union weakening (right)**: Weaken from right component of union.
-/
theorem weaken_union_right (h : Δ ⊢K φ) : (Γ ∪ Δ) ⊢K φ :=
  weakening (by intro a ha; exact Or.inr ha) h

/--
**Empty context weakening**: Theorems are provable in any context.

If ∅ ⊢ φ, then Γ ⊢ φ for any Γ.
-/
theorem weaken_empty (h : ∅ ⊢K φ) : Γ ⊢K φ :=
  weakening (by intro a ha; exact False.elim ha) h

------------------------------------------------------------------------------
-- § 2. Basic Derived Rules
------------------------------------------------------------------------------

/--
**Modus ponens as a lemma**: Convenient notation-friendly form.

From Γ ⊢ (φ ⊃ ψ) and Γ ⊢ φ, derive Γ ⊢ ψ.

**Why a lemma?** The mp constructor requires both derivations as arguments.
This lemma form is easier to use with Lean's term-mode tactics.

**Usage**: The workhorse of Hilbert-style proofs. Almost every non-trivial
step uses modus ponens.
-/
theorem modus_ponens (hφψ : Γ ⊢K (φ ⊃ ψ)) (hφ : Γ ⊢K φ) : Γ ⊢K ψ :=
  ProofK.mp hφψ hφ

/--
**Necessitation as a lemma**: Convenient notation-friendly form.

From Γ ⊢ φ, derive Γ ⊢ □φ.

**Why a lemma?** Makes it clear when we're "modalizing" a derivation.

**Important caveat**: Necessitation applies to full derivations, not to
mere assumptions! If φ ∈ Γ, we do NOT generally have □φ ∈ Γ.

**Usage**:
- Prove □-formulas by first proving the unboxed version
- Essential for modal reasoning
- Used in proving the modal distribution (K axiom application)
-/
theorem necessitation (h : Γ ⊢K φ) : Γ ⊢K □ φ := ProofK.nec h

/--
**Conjunction introduction**: From separate conjuncts, build conjunction.

From Γ ⊢ φ and Γ ⊢ ψ, derive Γ ⊢ (φ ∧ ψ).

**Proof strategy**: Use PL4 with two applications of modus ponens.
- PL4 gives us: φ ⊃ (ψ ⊃ (φ ∧ ψ))
- Apply MP with φ: ψ ⊃ (φ ∧ ψ)
- Apply MP with ψ: φ ∧ ψ

**Significance**: This is the standard introduction rule for conjunction,
derived from the Hilbert axioms.

**Usage**: Combine two proven facts into their conjunction.
-/
theorem and_intro (hφ : Γ ⊢K φ) (hψ : Γ ⊢K ψ) : Γ ⊢K (φ & ψ) := by
  exact ProofK.mp (ProofK.mp ProofK.pl4 hφ) hψ

/--
**Conjunction elimination (left)**: Extract left conjunct.

From Γ ⊢ (φ ∧ ψ), derive Γ ⊢ φ.

**Proof strategy**: Apply PL5 with modus ponens.

**Usage**: When you have a conjunction and need just one side.
-/
theorem and_elim_left (h : Γ ⊢K (φ & ψ)) : Γ ⊢K φ := by
  exact ProofK.mp ProofK.pl5 h

/--
**Conjunction elimination (right)**: Extract right conjunct.

From Γ ⊢ (φ ∧ ψ), derive Γ ⊢ ψ.

**Proof strategy**: Apply PL6 with modus ponens.

**Usage**: When you have a conjunction and need just one side.
-/
theorem and_elim_right (h : Γ ⊢K (φ & ψ)) : Γ ⊢K ψ := by
  exact ProofK.mp ProofK.pl6 h

/--
**K-distribution application**: Apply modal distribution.

From Γ ⊢ □(φ ⊃ ψ) and Γ ⊢ □φ, derive Γ ⊢ □ψ.

**Proof strategy**: Apply the K axiom twice with modus ponens.
- K gives: □(φ ⊃ ψ) ⊃ (□φ ⊃ □ψ)
- Apply MP with □(φ ⊃ ψ): □φ ⊃ □ψ
- Apply MP with □φ: □ψ

**Significance**: This is how we actually USE the K axiom in proofs.
It's the modal analog of function application.

**Usage**:
- Propagate necessity through implications
- The fundamental rule for modal reasoning
- Analogous to how modus ponens works for →

**Example reasoning**:
- If "φ implies ψ" is necessary (holds in all worlds)
- And φ is necessary (holds in all worlds)
- Then ψ is necessary (holds in all worlds)
-/
theorem k_app (h1 : Γ ⊢K □(φ ⊃ ψ)) (h2 : Γ ⊢K □φ) : Γ ⊢K □ ψ := by
  exact ProofK.mp (ProofK.mp ProofK.kdist h1) h2

------------------------------------------------------------------------------
-- § 3. Identity and Reflexivity
------------------------------------------------------------------------------

/--
**Identity axiom**: φ → φ is provable.

Every formula implies itself. This is the most basic tautology.

**Proof**: Uses PL1 and PL2 in a clever way:
1. PL2 gives: (φ → ((φ → φ) → φ)) → ((φ → (φ → φ)) → (φ → φ))
2. PL1 gives: φ → ((φ → φ) → φ)
3. PL1 gives: φ → (φ → φ)
4. Apply MP twice to get φ → φ
-/
theorem identity : Γ ⊢K (φ ⊃ φ) := by
  have h1 : Γ ⊢K ((φ ⊃ ((φ ⊃ φ) ⊃ φ)) ⊃ ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ))) :=
    ProofK.pl2
  have h2 : Γ ⊢K (φ ⊃ ((φ ⊃ φ) ⊃ φ)) := ProofK.pl1
  have h3 : Γ ⊢K ((φ ⊃ (φ ⊃ φ)) ⊃ (φ ⊃ φ)) := ProofK.mp h1 h2
  have h4 : Γ ⊢K (φ ⊃ (φ ⊃ φ)) := ProofK.pl1
  exact ProofK.mp h3 h4

/--
**Reflexivity is a simp lemma**: Useful for automation.
-/
@[simp] theorem identity_simp : Γ ⊢K (φ ⊃ φ) := identity

------------------------------------------------------------------------------
-- § 4. Implication Chains
------------------------------------------------------------------------------

/--
**Implication chain (2 steps)**: (φ → ψ) → (ψ → χ) → (φ → χ)

Transitivity of implication.
-/
theorem impl_chain2
    (h1 : Γ ⊢K (φ ⊃ ψ))
    (h2 : Γ ⊢K (ψ ⊃ χ)) :
    Γ ⊢K (φ ⊃ χ) :=
  ProofK.mp
    (ProofK.mp
      ProofK.pl2
      (ProofK.mp ProofK.pl1 h2))
    h1


/--
**Implication transitivity**: Direct form.

If φ → ψ and ψ → χ, then φ → χ.
-/
theorem impl_trans (h1 : Γ ⊢K (φ ⊃ ψ)) (h2 : Γ ⊢K (ψ ⊃ χ)) :
    Γ ⊢K (φ ⊃ χ) :=
  impl_chain2 h1 h2

------------------------------------------------------------------------------
-- § 5. Context Manipulation
------------------------------------------------------------------------------

/- NOTE: The deduction theorem, `singleton_mp`, and `context_split` have been removed.
   The standard deduction theorem does NOT hold for modal logic K without restrictions.
   The problem is the necessitation rule: from `(Γ ∪ {φ}) ⊢K □χ` (obtained via `nec`
   applied to `(Γ ∪ {φ}) ⊢K χ`), we cannot in general derive `Γ ⊢K (φ ⊃ □χ)`,
   because necessitation requires the premise to be a *theorem* (provable from the empty
   context or from Γ alone), not merely derivable from assumptions that include φ.

   A correct restricted deduction theorem would require tracking that φ does not appear
   in the scope of any application of the necessitation rule. Since `ProofK` does not track
   this side condition, the theorem cannot be stated correctly in this framework.

   The converse direction (`conv_deduction`) works unconditionally and is in
   `SyntaxLemmas.lean`.
-/

/--
**Context union is associative** (up to provable equivalence).
-/
theorem context_union_assoc (h : ((Γ ∪ Δ) ∪ Θ) ⊢K φ) :
    (Γ ∪ (Δ ∪ Θ)) ⊢K φ := by
  apply weakening (φ := φ) _ h
  intro a ha
  simp [Set.mem_union] at ha ⊢
  -- ha : (a ∈ Γ ∨ a ∈ Δ) ∨ a ∈ Θ
  -- need: a ∈ Γ ∨ (a ∈ Δ ∨ a ∈ Θ)
  cases ha with
  | inl h1 =>
      cases h1 with
      | inl hΓ => exact Or.inl hΓ
      | inr hΔ => exact Or.inr (Or.inl hΔ)
  | inr hΘ => exact Or.inr (Or.inr hΘ)

/--
**Context union is commutative** (up to provable equivalence).
-/
theorem context_union_comm (h : (Γ ∪ Δ) ⊢K φ) :
    (Δ ∪ Γ) ⊢K φ := by
  apply weakening (φ := φ) _ h
  intro a ha
  simp [Set.mem_union] at ha ⊢
  cases ha with
  | inl hl => exact Or.inr hl
  | inr hr => exact Or.inl hr

------------------------------------------------------------------------------
-- § 6. Useful Combinations
------------------------------------------------------------------------------

/--
**Weakening with modus ponens**: Common pattern.

If Γ ⊢ φ → ψ and Δ ⊢ φ, then (Γ ∪ Δ) ⊢ ψ.
-/
theorem weaken_mp (h1 : Γ ⊢K (φ ⊃ ψ)) (h2 : Δ ⊢K φ) :
    (Γ ∪ Δ) ⊢K ψ := by
  have h1' : (Γ ∪ Δ) ⊢K (φ ⊃ ψ) := weaken_union_left (Δ := Δ) h1
  have h2' : (Γ ∪ Δ) ⊢K φ := weaken_union_right (Γ := Γ) h2
  exact ProofK.mp h1' h2'

/--
**Repeated weakening**: Add multiple formulas to context.
-/
theorem weaken_insert_list (h : Γ ⊢K φ) (L : List Form) :
    (Γ ∪ {x | x ∈ L}) ⊢K φ := by
  apply weakening
  · intro a ha
    exact Or.inl ha
  · exact h

/--
**Necessitation preserves weakening**.
-/
theorem nec_weaken (hsub : ∀ ⦃a⦄, a ∈ Γ → a ∈ Δ) (h : Γ ⊢K φ) :
    Δ ⊢K □ φ :=
  ProofK.nec (weakening hsub h)

/--
**Conjunction introduction alias**: From Γ ⊢ φ and Γ ⊢ ψ, derive Γ ⊢ (φ & ψ).

Alias for `and_intro`; provided for naming symmetry with `and_elim_left/right`.
-/
theorem and_intro_weaken (h1 : Γ ⊢K φ) (h2 : Γ ⊢K ψ) : Γ ⊢K (φ & ψ) :=
  and_intro h1 h2

end ProofK

end BasicModal
