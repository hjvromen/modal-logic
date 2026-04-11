import ModalLogic.Semantics.Soundness
import ModalLogic.Syntax.SyntaxLemmas
import Mathlib.Order.Zorn

/-!
# Consistency, Maximal Consistent Sets, and Lindenbaum's Lemma

This file establishes the foundation for proving strong completeness of standard normal modal
logics (K, T, S4, S5) via the canonical model construction.

## Main Results

The development proceeds in the following stages:

1. **Semantic Consistency**: We show that standard modal logics are semantically consistent,
   meaning they have models where not everything is provable.

2. **Finite Conjunctions**: We define `fin_conj` to express "all formulas in a finite list hold"
   and prove its key properties for manipulating derivations.

3. **Axiomatic Consistency**: We define what it means for a set of formulas to be consistent
   relative to an axiom system, and characterize maximal consistent sets.

4. **Lindenbaum's Lemma**: Using Zorn's lemma, we prove every consistent set extends to a
   maximally consistent set - the key ingredient for canonical models.

## Strategy Overview

The completeness proof follows the standard Henkin-style approach:
- Start with an unprovable formula φ
- Build a consistent set Γ that doesn't contain φ
- Extend Γ to a maximally consistent set Γ' (Lindenbaum)
- Construct a canonical model from all maximally consistent sets
- Show φ fails in this model (via the Truth Lemma)
- Conclude φ is not semantically valid

## References

The proof strategy follows standard developments found in:
- Blackburn, de Rijke, Venema: "Modal Logic" (2001), Chapter 4
- Hughes & Cresswell: "A New Introduction to Modal Logic" (1996)
- Chellas: "Modal Logic: An Introduction" (1980)
-/

open Classical
--open Modal
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

------------------------------------------------------------------------------
-- § 1. Semantic Consistency
------------------------------------------------------------------------------

/--
A set of axioms AX is **semantically consistent** if it does not globally entail falsehood.
In other words, there exists a model where all axioms in AX are true at some world.
This is the semantic counterpart to syntactic consistency (not proving ⊥).
-/
def sem_cons (AX : Ctx) : Prop := ¬ (globalSemCsq AX Form.bot)

/--
**Semantic Consistency of K**: The minimal modal logic K is semantically consistent.
We witness this by constructing a trivial model where all propositions are true.
-/
lemma sem_consK : sem_cons ∅ := by
  rw [sem_cons, globalSemCsq]
  push_neg
  -- Construct a simple frame: natural numbers with equality as accessibility
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  -- All propositions are true at all worlds in this valuation
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · -- No axioms to satisfy (empty set)
    intro φ x h1
    exact False.elim h1
  · -- Witness: world 42 doesn't force ⊥
    use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of T**: The reflexive modal logic T is semantically consistent.
T adds the axiom □φ ⊃ φ, which is valid in reflexive frames.
-/
lemma sem_consT : sem_cons TAxioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  -- Use the same simple reflexive frame (equality)
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · -- T axiom: □ψ ⊃ ψ holds in reflexive frames
    intro φ x h1
    obtain ⟨ψ, h1⟩ := h1
    subst h1
    intro h1
    apply h1 x rfl
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of S4**: S4 = T + transitivity is semantically consistent.
S4 adds □φ ⊃ □□φ, valid in transitive frames.
-/
lemma sem_consS4 : sem_cons S4Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · -- S4 axioms: T + (□ψ ⊃ □□ψ)
    intro φ x h1
    simp only [S4Axioms, Set.mem_union, Set.mem_setOf_eq] at h1
    cases h1 with
    | inl h1 => -- T axiom
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1
      apply h1 x rfl
    | inr h1 => -- 4 axiom: □ψ ⊃ □□ψ
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1 y hxy z hyz
      apply h1 z
      rw [hxy, hyz]
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of S5**: S5 = T + symmetry + transitivity is semantically consistent.
S5 adds ◇φ ⊃ □◇φ, valid in equivalence relation frames.
-/
lemma sem_consS5 : sem_cons S5Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · -- S5 axioms: T + (◇ψ ⊃ □◇ψ), equivalently (¬□¬ψ ⊃ □¬□¬ψ)
    intro φ x h1
    simp only [S5Axioms, Set.mem_union, Set.mem_setOf_eq] at h1
    cases h1 with
    | inl h1 => -- T axiom
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1
      apply h1 x rfl
    | inr h1 => -- 5 axiom
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1 y hxy
      rw [← hxy]
      exact h1
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KD**: KD adds the D axiom □φ ⊃ ◇φ, valid in serial frames.
-/
lemma sem_consKD : sem_cons KDAxioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  -- Use the natural numbers with successor relation (serial but not reflexive)
  let f : Frame := ⟨ℕ, fun x y => y = x + 1⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · -- KD axiom: □ψ ⊃ ◇ψ holds in serial frames
    intro φ x h1
    obtain ⟨ψ, h1⟩ := h1
    subst h1
    intro h1
    -- □ψ at x means ψ holds at all successors
    -- We need to show ◇ψ, i.e., ¬□¬ψ
    -- There exists a successor x+1, and ψ holds there
    simp [forces, dia, neg]
    exact ⟨x + 1, rfl, h1 (x + 1) rfl⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KB**: KB adds the B axiom φ ⊃ □◇φ, valid in symmetric frames.
-/
lemma sem_consK4 : sem_cons K4Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    obtain ⟨ψ, h1⟩ := h1
    subst h1
    intro h1 y hxy z hyz
    apply h1 z
    rw [hxy, hyz]
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KTB**: KTB adds T + B axioms, valid in reflexive-symmetric frames.
-/
lemma sem_consKTB : sem_cons KTBAxioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KTBAxioms, Set.mem_union, Set.mem_setOf_eq] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1
      apply h1 x rfl
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hψ y hxy
      simp [forces, dia, neg]
      exact ⟨x, hxy.symm, hψ⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KB4**: KB4 adds B + 4 axioms, valid in symmetric-transitive frames.
-/
lemma sem_consKB4 : sem_cons KB4Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KB4Axioms, Set.mem_union, Set.mem_setOf_eq] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hψ y hxy
      simp [forces, dia, neg]
      exact ⟨x, hxy.symm, hψ⟩
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1 y hxy z hyz
      apply h1 z
      rw [hxy, hyz]
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KB**: KB adds the B axiom φ ⊃ □◇φ, valid in symmetric frames.
-/
lemma sem_consKB : sem_cons KBAxioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  -- Use the natural numbers with equality as accessibility (symmetric)
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · -- KB axiom: ψ ⊃ □◇ψ holds in symmetric frames
    intro φ x h1
    obtain ⟨ψ, h1⟩ := h1
    subst h1
    intro hψ y hxy
    -- Need to show ◇ψ at y, i.e., ∃z, R(y,z) ∧ ψ at z
    -- By symmetry R(y,x), and ψ at x
    simp [forces, dia, neg]
    exact ⟨x, hxy.symm, hψ⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of K5**: K5 adds the 5 axiom ◇φ ⊃ □◇φ, valid in Euclidean frames.
-/
lemma sem_consK5 : sem_cons K5Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    obtain ⟨ψ, h1⟩ := h1
    subst h1
    intro hDia y hxy
    simp [forces, dia, neg] at hDia ⊢
    obtain ⟨z, hxz, hz⟩ := hDia
    exact ⟨z, by rw [← hxy]; exact hxz, hz⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KD5**: KD5 adds D + 5 axioms, valid in serial Euclidean frames.
-/
lemma sem_consKD5 : sem_cons KD5Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KD5Axioms, Set.mem_union, Set.mem_setOf_eq] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hBox
      simp [forces, dia, neg]
      exact ⟨x, rfl, hBox x rfl⟩
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hDia y hxy
      simp [forces, dia, neg] at hDia ⊢
      obtain ⟨z, hxz, hz⟩ := hDia
      exact ⟨z, by rw [← hxy]; exact hxz, hz⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KD45**: KD45 adds D + 4 + 5 axioms, valid in serial transitive Euclidean frames.
-/
lemma sem_consKD45 : sem_cons KD45Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KD45Axioms, Set.mem_union] at h1
    rcases h1 with (h1 | h1) | h1
    · obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hBox
      simp [forces, dia, neg]
      exact ⟨x, rfl, hBox x rfl⟩
    · obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1 y hxy z hyz
      apply h1 z
      rw [hxy, hyz]
    · obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hDia y hxy
      simp [forces, dia, neg] at hDia ⊢
      obtain ⟨z, hxz, hz⟩ := hDia
      exact ⟨z, by rw [← hxy]; exact hxz, hz⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KDB**: KDB adds D + B axioms, valid in serial symmetric frames.
-/
lemma sem_consKDB : sem_cons KDBAxioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KDBAxioms, Set.mem_union] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hBox
      simp [forces, dia, neg]
      exact ⟨x, rfl, hBox x rfl⟩
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hψ y hxy
      simp [forces, dia, neg]
      exact ⟨x, hxy.symm, hψ⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KD4**: KD4 adds D + 4 axioms, valid in serial transitive frames.
-/
lemma sem_consKD4 : sem_cons KD4Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KD4Axioms, Set.mem_union] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hBox
      simp [forces, dia, neg]
      exact ⟨x, rfl, hBox x rfl⟩
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1 y hxy z hyz
      apply h1 z
      rw [hxy, hyz]
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of K45**: K45 adds 4 + 5 axioms, valid in transitive Euclidean frames.
-/
lemma sem_consK45 : sem_cons K45Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [K45Axioms, Set.mem_union] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro h1 y hxy z hyz
      apply h1 z
      rw [hxy, hyz]
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hDia y hxy
      simp [forces, dia, neg] at hDia ⊢
      obtain ⟨z, hxz, hz⟩ := hDia
      exact ⟨z, by rw [← hxy]; exact hxz, hz⟩
  · use 42
    rw [forces]
    trivial

/--
**Semantic Consistency of KB5**: KB5 adds B + 5 axioms, valid in symmetric Euclidean frames.
-/
lemma sem_consKB5 : sem_cons KB5Axioms := by
  rw [sem_cons, globalSemCsq]
  push_neg
  let f : Frame := ⟨ℕ, Eq⟩
  use f
  let v := fun (_ : ℕ) (_ : ℕ) => True
  use v
  constructor
  · intro φ x h1
    simp only [KB5Axioms, Set.mem_union] at h1
    cases h1 with
    | inl h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hψ y hxy
      simp [forces, dia, neg]
      exact ⟨x, hxy.symm, hψ⟩
    | inr h1 =>
      obtain ⟨ψ, h1⟩ := h1
      subst h1
      intro hDia y hxy
      simp [forces, dia, neg] at hDia ⊢
      obtain ⟨z, hxz, hz⟩ := hDia
      exact ⟨z, by rw [← hxy]; exact hxz, hz⟩
  · use 42
    rw [forces]
    trivial

/--
**Syntactic consequence of semantic consistency**: If AX is semantically consistent,
then it doesn't prove ⊥. This follows from the soundness theorem.
-/
lemma nprfalse (AX : Ctx) (hax : sem_cons AX) : ¬ ProofK AX Form.bot := by
  have h1 : ¬ globalSemCsq AX Form.bot → ¬ ProofK AX Form.bot := by
    have h2 : ProofK AX Form.bot → globalSemCsq AX Form.bot := soundness AX Form.bot
    exact mt h2
  apply h1
  rw [sem_cons] at hax
  exact hax

/--
**Negation consistency**: In a consistent system, proving ¬φ excludes proving φ.
-/
lemma prnot_to_notpr (φ : Form) (AX : Ctx) (hax : sem_cons AX) :
  ProofK AX (∼φ) → ¬ ProofK AX φ := by
  intro h1
  by_contra h2
  -- From φ and ¬φ we can derive ⊥
  exact absurd (mp (mp pl5 contra_equiv_false) (mp (mp pl4 h2) h1)) (nprfalse AX hax)

/--
**Dual of negation consistency**: In a consistent system, proving φ excludes proving ¬φ.
-/
lemma pr_to_notprnot (φ : Form) (AX : Ctx) (hax : sem_cons AX) :
  ProofK AX φ → ¬ ProofK AX (∼φ) := by
  have h1 := prnot_to_notpr φ AX hax
  intro h2
  apply mt h1
  push_neg
  exact h2

------------------------------------------------------------------------------
-- § 2. Finite Conjunctions
------------------------------------------------------------------------------

/--
**Finite conjunction operator**: Conjoin all formulas in a list.
- Empty list: ⊤ (trivially true)
- Non-empty: φ₁ ∧ φ₂ ∧ ... ∧ φₙ (right-associative)

This provides a syntactic way to express "all formulas in L hold simultaneously".
-/
def fin_conj : List Form → Form
  | []      => ⊤ₘ
  | (φ::φs) => φ & (fin_conj φs)

/-- Base case: empty conjunction is ⊤. -/
@[simp] lemma fin_conj_nil : fin_conj ([] : List Form) = ⊤ₘ := rfl

/-- Recursive case: conjoin head with tail. -/
@[simp] lemma fin_conj_cons (φ : Form) (L : List Form) :
  fin_conj (φ :: L) = φ & fin_conj L := rfl

-- Lemmas about finite conjunctions and provability

/-- **Contradiction**: The list [ψ, ¬ψ] proves its own negation. -/
lemma fin_conj_simp {Γ : Ctx} : ∀ ψ : Form, ProofK Γ (∼(fin_conj [ψ, ∼ψ])) := by
  intro ψ
  exact (not_and_subst phi_and_true).mpr not_contra

/--
**Implication-conjunction exchange**:
(φ ∧ L ⊃ ψ) ↔ (L ⊃ (φ ⊃ ψ))

This is the syntactic version of currying.
-/
lemma imp_conj_imp_imp {Γ : Ctx} {φ ψ : Form} {L : List Form} :
  ProofK Γ ((fin_conj (φ::L)) ⊃ ψ) ↔ ProofK Γ (fin_conj L ⊃ (φ ⊃ ψ)) := by
  constructor
  · intro h
    simp only [fin_conj] at h
    rw [and_right_imp] at h
    exact h
  · intro h
    simp only [fin_conj]
    rw [and_right_imp]
    exact h

/-- **Weakening for conjunctions**: If φ ∧ L ⊢ φ ⊃ b, then L ⊢ φ ⊃ b. -/
lemma fin_conj_cons_imp {Γ : Ctx} {φ b : Form} {L : List Form} :
  ProofK Γ (fin_conj (φ::L) ⊃ (φ ⊃ b)) → ProofK Γ (fin_conj L ⊃ (φ ⊃ b)) := by
  intro h
  rw [imp_conj_imp_imp] at h
  rw [imp_imp_iff_imp] at h
  exact h

/-
**Conjunction distributes over append**:
(fin_conj L' ∧ fin_conj L) ↔ fin_conj (L' ++ L)
-/
lemma fin_conj_append {Γ : Ctx} {L L' : List Form} :
  ProofK Γ ((fin_conj L' & fin_conj L) ⇔ (fin_conj (L' ++ L))) := by
  induction L' with
  | nil =>
    -- Base: ⊤ ∧ fin_conj L ↔ fin_conj L
    rw [fin_conj]
    exact (mp (mp pl4 (cut (mp pl6 and_switch) (mp pl5 phi_and_true)))
      (cut (mp pl6 phi_and_true) (mp pl5 and_switch)))
  | cons hd tl ih =>
    -- Step: use associativity and induction
    have h_assoc : Γ ⊢K (hd & fin_conj tl) ⋏ fin_conj L ⇔ hd & (fin_conj tl ⋏ fin_conj L) := by
      convert BasicModal.and_assoc using 1
    simp +zetaDelta at *
    -- Forward direction
    have hfwd : Γ ⊢K (hd ⋏ fin_conj tl ⋏ fin_conj L ⟹ hd ⋏ fin_conj (tl ++ L)) := by
      have h1 : Γ ⊢K (fin_conj tl ⋏ fin_conj L ⟹ fin_conj (tl ++ L)) :=
        and_elim_left ih
      have h2 : Γ ⊢K (hd ⋏ fin_conj tl ⋏ fin_conj L ⟹ hd ⋏ (fin_conj tl ⋏ fin_conj L)) :=
        and_elim_left h_assoc
      have h3 : Γ ⊢K (hd ⋏ (fin_conj tl ⋏ fin_conj L) ⟹ hd ⋏ fin_conj (tl ++ L)) :=
        imp_and_imp h1
      exact impl_chain2 h2 h3
    -- Backward direction
    have hbwd : Γ ⊢K (hd ⋏ fin_conj (tl ++ L) ⟹ hd ⋏ fin_conj tl ⋏ fin_conj L) := by
      have h1 : Γ ⊢K (fin_conj (tl ++ L) ⟹ fin_conj tl ⋏ fin_conj L) :=
        and_elim_right ih
      have h2 : Γ ⊢K (hd ⋏ fin_conj (tl ++ L) ⟹ hd ⋏ (fin_conj tl ⋏ fin_conj L)) :=
        imp_and_imp h1
      have h3 : Γ ⊢K (hd ⋏ (fin_conj tl ⋏ fin_conj L) ⟹ hd ⋏ fin_conj tl ⋏ fin_conj L) :=
        and_elim_right h_assoc
      exact impl_chain2 h2 h3
    exact and_intro hfwd hbwd

/--
**Empty conjunction doesn't prove falsity**: In a consistent system,
⊤ ⊃ ⊥ is not provable.
-/
lemma fin_conj_empty {AX : Ctx} {L : List Form} (hax : sem_cons AX) :
  L = [] → ¬ ProofK AX (fin_conj L ⊃ ⊥ₘ) := by
  intro h1
  subst h1
  by_contra h2
  -- From ⊤ ⊃ ⊥ and ⊤, derive ⊥
  have h3 : ProofK AX Form.bot := mp h2 identity
  exact (nprfalse AX hax) h3

/-- **Helper**: If all elements of L equal θ, then θ implies their conjunction. -/
lemma fin_conj_repeat_helper {AX : Ctx} {θ : Form} {L : List Form} :
  (∀ ψ ∈ L, ψ = θ) → ProofK AX (θ ⊃ fin_conj L) := by
  intro h1
  induction L with
  | nil => exact mp pl1 identity  -- θ ⊃ ⊤
  | cons hd tl ih =>
    simp at *
    obtain ⟨h1, h2⟩ := h1
    subst h1
    -- θ ⊃ (θ ∧ fin_conj tl)
    exact cut (mp double_imp pl4) (imp_and_and_imp (mp (mp pl4 identity) (ih h2)))

/--
**Repeated negation**: If L = [¬φ, ¬φ, ..., ¬φ] and we prove ¬(conjunction),
then we can prove φ.
-/
lemma fin_conj_repeat {AX : Ctx} {φ : Form} {L : List Form} (hax : sem_cons AX) :
  (∀ ψ ∈ L, ψ = ∼φ) → ProofK AX (∼(fin_conj L)) → ProofK AX φ := by
  intro h1 h2
  induction L with
  | nil =>
    -- Impossible: ¬⊤ proves φ, but ¬⊤ ≡ ⊥
    exact absurd (mp dne h2) (nprfalse AX hax)
  | cons hd tl _ =>
    simp at *
    obtain ⟨h1, h3⟩ := h1
    have h4 : ProofK AX ((∼φ) ⊃ fin_conj tl) := fin_conj_repeat_helper h3
    have h5 : ProofK AX ((∼(fin_conj tl)) ⊃ (∼∼φ)) := contrapos.mpr h4
    subst h1
    exact (mp (mp peirce_variant (contrapos.mpr (cut h5 dne)))
      (contrapos.mpr (cut ((demorgans.mp) (mp (mp pl6 (iff_not and_switch)) h2)) dne)))

/-- **Box distributes over binary conjunction**: □φ ∧ □ψ ⊢ □(φ ∧ ψ). -/
lemma fin_conj_box2 {AX : Ctx} {φ ψ : Form} :
  ProofK AX ((□φ & □ψ) ⊃ □(φ & ψ)) := by
  exact (mp double_imp (cut2 pl6 (cut pl5 (cut (mp kdist (nec pl4)) kdist))))

/--
**Box distributes over n-ary conjunction**:
□φ₁ ∧ ... ∧ □φₙ ⊢ □(φ₁ ∧ ... ∧ φₙ)
-/
lemma fin_conj_boxn {AX : Ctx} {L : List Form} :
  ProofK AX ((fin_conj (List.map (fun x => □x) L)) ⊃ (□(fin_conj L))) := by
  induction L with
  | nil => exact (mp pl1 (nec prtrue))  -- ⊤ ⊢ □⊤
  | cons hd tl ih => exact (cut (imp_and_imp ih) fin_conj_box2)

/-- **Technical helper**: If L has elements and Γ is empty, then L must be empty. -/
lemma listempty {Γ : Ctx} {L : List Form} :
  (∀ φ ∈ L, φ ∈ Γ) → Γ = ∅ → L = [] := by
  intro h1 h2
  by_contra h3
  obtain ⟨φ, h5⟩ := List.exists_mem_of_length_pos (List.length_pos_of_ne_nil h3)
  rw [h2] at h1
  exact absurd (h1 φ h5) (by simp)

------------------------------------------------------------------------------
-- § 3. Axiomatic Consistency
------------------------------------------------------------------------------

/--
**Finite axiomatic consistency**: A finite list L is AX-consistent if
its conjunction doesn't prove ⊥ in the system AX.
-/
def fin_ax_consist (AX : Ctx) (L : List Form) := ¬ (ProofK AX (fin_conj L ⊃ ⊥ₘ))

/--
**Axiomatic consistency**: A set Γ is AX-consistent if every finite subset L ⊆ Γ
is finitely AX-consistent.

This is the compactness property: Γ is consistent iff all its finite subsets are.
-/
def ax_consist (AX Γ : Ctx) :=
  ∀ L : List Form, (∀ ψ ∈ L, ψ ∈ Γ) → fin_ax_consist AX L

/--
**Maximal axiomatic consistency**: Γ is maximally AX-consistent if:
1. Γ is AX-consistent
2. Every proper superset of Γ is AX-inconsistent

Equivalently: Γ is a maximal element in the poset of consistent sets.
-/
def max_ax_consist (AX Γ : Ctx) :=
  ax_consist AX Γ ∧ (∀ Γ', Γ ⊂ Γ' → ¬ ax_consist AX Γ')

/-- **Maximal consistency implies consistency**. -/
lemma max_imp_ax {AX Γ : Ctx} : max_ax_consist AX Γ → ax_consist AX Γ := by
  intro h1
  exact h1.left

------------------------------------------------------------------------------
-- § 4. Key Technical Lemmas
------------------------------------------------------------------------------

/--
**Lemma 5 (Helper)**: Technical decomposition lemma for separating φ from context Γ.

If every formula in L is either in Γ or equals φ, and L proves b,
then we can extract a subset L' ⊆ Γ that proves φ ⊃ b.

This is used to show: if Γ ∪ {φ} is inconsistent, then Γ proves ¬φ.
-/
lemma five_helper (AX : Ctx) :
  ∀ Γ : Ctx, ∀ φ : Form, ∀ L : List Form, ∀ b : Form,
  (∀ ψ ∈ L, (ψ ∈ Γ) ∨ (ψ = φ)) → ProofK AX (fin_conj L ⊃ b) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ ProofK AX (fin_conj L' ⊃ (φ ⊃ b)) := by
  intro Γ φ L b h1 h2
  revert b
  induction L with
  | nil =>
    -- Base case: empty list
    intro b h2
    use ([] : List Form)
    constructor
    · intro ψ h3
      cases h3  -- impossible: no elements in empty list
    · exact imp_if_imp_imp h2
  | cons hd tl ih =>
    intro b h2
    have h1a : ∀ (ψ : Form), ψ ∈ tl → (ψ ∈ Γ) ∨ (ψ = φ) := by
      intro ψ h2
      apply h1 ψ (List.mem_cons_of_mem hd h2)
    have h1b : (hd ∈ Γ) ∨ (hd = φ) := by
      apply h1 hd
      left
    cases h1b with
    | inl h1b => -- hd ∈ Γ: keep it in the result
      have h3 := and_right_imp.mp h2
      obtain ⟨L', ih⟩ := ih h1a (hd ⊃ b) h3
      use (hd::L' : List Form)
      obtain ⟨ih_left, ih_right⟩ := ih
      constructor
      · intro ψ h4
        cases h4 with
        | head => exact h1b
        | tail _ h4 => apply ih_left ψ h4
      · rw [imp_shift] at ih_right
        rw [← imp_conj_imp_imp] at ih_right
        exact ih_right
    | inr h1b => -- hd = φ: use it to strengthen the conclusion
      have h5 : ProofK AX (fin_conj tl ⊃ (φ ⊃ b)) := h1b ▸ (and_right_imp.mp h2)
      obtain ⟨L', ih⟩ := ih h1a (φ ⊃ b) h5
      use (L' : List Form)
      constructor
      · exact ih.left
      · exact imp_imp_iff_imp.mp ih.right

/--
**Lemma 5 (Deduction Principle)**: If Γ ∪ {φ} is inconsistent,
then some finite subset of Γ proves ¬φ.

This is essentially a semantic deduction theorem for consistency.
-/
lemma five (AX : Ctx) :
  ∀ Γ : Ctx, ∀ φ : Form, ¬ ax_consist AX (Γ ∪ {φ}) → ∃ L',
  (∀ ψ ∈ L', ψ ∈ Γ) ∧ ProofK AX (fin_conj L' ⊃ (∼φ)) := by
  intro Γ φ h1
  rw [ax_consist] at h1
  push_neg at h1
  obtain ⟨L, h1⟩ := h1
  have h2 := five_helper AX Γ φ L Form.bot
  obtain ⟨h1_left, h1_right⟩ := h1
  have h3 : (∀ (ψ : Form), ψ ∈ L → (ψ ∈ Γ) ∨ ψ = φ) := by
    intro ψ this
    have hmem : ψ ∈ Γ ∪ {φ} := h1_left ψ this
    rw [Set.mem_union, Set.mem_singleton_iff] at hmem
    exact hmem
  apply h2 h3
  rw [fin_ax_consist] at h1_right
  push_neg at h1_right
  exact h1_right

/--
**Lemma 6 (Helper)**: In a maximally consistent set, the law of excluded middle holds:
for every φ, either φ ∈ Γ or ¬φ ∈ Γ.
-/
lemma six_helper (AX Γ : Ctx) :
  max_ax_consist AX Γ → ∀ φ : Form, (φ ∈ Γ) ∨ (∼φ) ∈ Γ := by
  intro h1 φ
  rw [or_iff_not_and_not]
  by_contra h2
  obtain ⟨h2l, h2r⟩ := h2
  obtain ⟨h1l, h1r⟩ := h1
  have h2 := h1r (Γ ∪ {φ})
  have h3 := h1r (Γ ∪ {∼φ})
  -- Both Γ ∪ {φ} and Γ ∪ {¬φ} are inconsistent by maximality
  have h4 : ¬ ax_consist AX (Γ ∪ {∼φ}) := by
    apply h3
    simpa [Set.union_singleton] using Set.ssubset_insert h2r
  have h5 : ¬ ax_consist AX (Γ ∪ {φ}) := by
    apply h2
    simpa [Set.union_singleton] using Set.ssubset_insert h2l
  clear h2 h3
  -- Apply Lemma 5 to both branches
  obtain ⟨L', h6⟩ := five AX Γ φ h5
  obtain ⟨L, h7⟩ := five AX Γ (∼φ) h4
  obtain ⟨h6l, h6r⟩ := h6
  obtain ⟨h7l, h7r⟩ := h7
  -- Combine to get contradiction: L' proves ¬φ and L proves φ
  -- First combine into a conjunction: (¬φ ∧ ¬¬φ)
  have h8 := imp_and_and_imp (mp (mp pl4 h6r) h7r)
  -- (¬φ ∧ ¬¬φ) is equivalent to (¬φ ∧ φ) by double negation
  -- And (¬φ ∧ φ) ↔ ⊥ (after swapping to (φ ∧ ¬φ))
  have h12 := cut (mp pl6 fin_conj_append) (cut h8 (mp pl5 contra_equiv_false))
  have h13 : (∀ (ψ : Form), ψ ∈ L' ++ L → ψ ∈ Γ) := by
    intro ψ h13
    rw [List.mem_append] at h13
    cases h13 with
    | inl h13 => exact (h6l ψ) h13
    | inr h13 => exact (h7l ψ) h13
  exact absurd h12 ((h1l (L' ++ L)) h13)

/--
**Lemma 6 (Characterization of Maximal Consistency)**:
Γ is maximally AX-consistent if and only if for every formula φ,
exactly one of {φ, ¬φ} is in Γ.

This gives a semantic characterization: maximal consistent sets are "complete theories"
that decide every formula.
-/
lemma six (AX Γ : Ctx) (h : ax_consist AX Γ) :
  max_ax_consist AX Γ ↔ ∀ φ, ((φ ∈ Γ) ∨ (∼φ) ∈ Γ) ∧ ¬(φ ∈ Γ ∧ (∼φ) ∈ Γ) := by
  constructor
  · -- (→) Maximal ⇒ decides every formula
    intro h1 φ
    constructor
    · -- Excluded middle: φ ∨ ¬φ ∈ Γ
      exact six_helper (AX:=AX) (Γ:=Γ) h1 φ
    · -- Not both: ¬(φ ∈ Γ ∧ ¬φ ∈ Γ)
      intro hboth
      rcases hboth with ⟨hφ, hnotφ⟩
      have all_in : ∀ ψ ∈ ([φ, ∼φ] : List Form), ψ ∈ Γ := by
        intro ψ hψ
        simp at hψ
        rcases hψ with hψ | hψ
        · subst hψ; exact hφ
        · subst hψ; exact hnotφ
      have hfin : fin_ax_consist AX [φ, ∼φ] := h [φ, ∼φ] all_in
      exact hfin (fin_conj_simp φ)
  · -- (←) Decides every formula ⇒ maximal
    intro hdec
    constructor
    · -- Γ is consistent (given as hypothesis h)
      exact h
    · -- Show maximality: any proper superset is inconsistent
      intro Γ' hproper
      rcases hproper with ⟨hsub, hnot_sub⟩
      -- Find witness ψ ∈ Γ' \ Γ
      rcases Set.not_subset.mp hnot_sub with ⟨ψ, hψΓ', hψnotΓ⟩
      -- By decidability, we know either ψ ∈ Γ or ¬ψ ∈ Γ
      have hdisj : (ψ ∈ Γ) ∨ (∼ψ) ∈ Γ := (hdec ψ).1
      -- Since ψ ∉ Γ, we must have ¬ψ ∈ Γ
      have hnotψΓ : (∼ψ) ∈ Γ := by
        cases hdisj with
        | inl hψΓ => exact (hψnotΓ hψΓ).elim
        | inr h => exact h
      -- So Γ' contains both ψ and ¬ψ (since Γ ⊆ Γ')
      have hnotψΓ' : (∼ψ) ∈ Γ' := Set.mem_of_subset_of_mem hsub hnotψΓ
      -- Hence Γ' is inconsistent: it contains both ψ and ¬ψ
      rw [ax_consist]
      push_neg
      refine ⟨([ψ, ∼ψ] : List Form), ?_, ?_⟩
      · -- Show all elements of [ψ, ¬ψ] are in Γ'
        intro χ hχ
        simp at hχ
        rcases hχ with hχ | hχ
        · subst hχ; exact hψΓ'
        · subst hχ; exact hnotψΓ'
      · -- Show [ψ, ¬ψ] is inconsistent
        rw [fin_ax_consist]
        push_neg
        exact fin_conj_simp ψ

------------------------------------------------------------------------------
-- § 5. Lindenbaum's Lemma (Existence of Maximal Extensions)
------------------------------------------------------------------------------

/--
**Chain helper for Lindenbaum**: If every formula in a finite list L appears
somewhere in a chain c, then all formulas appear together in some single element of c.

This uses the chain property: any two elements are comparable, so we can find
a common upper bound containing all formulas.
-/
lemma lindenhelper
  (c : Set Ctx) (h : c.Nonempty) (h1 : IsChain (· ⊆ ·) c) (L : List Form) :
  (∀ φ ∈ L, φ ∈ ⋃₀ c) → ∃ m ∈ c, (∀ ψ ∈ L, ψ ∈ m) := by
  intro h2
  induction L with
  | nil =>
    -- Empty list: pick any element from the chain
    rcases h with ⟨m, hm⟩
    refine ⟨m, hm, ?_⟩
    intro ψ hmem; cases hmem  -- impossible: no elements in empty list
  | cons hd tl ih =>
    -- Get element m containing all of tl (by IH)
    have h2_tl : ∀ φ ∈ tl, φ ∈ ⋃₀ c := by
      intro φ hφ
      exact h2 φ (List.mem_cons_of_mem hd hφ)
    rcases ih h2_tl with ⟨m, hm, htl⟩
    -- Get element m' containing hd
    have h_hd_in_sUnion : hd ∈ ⋃₀ c := h2 hd (by simp)
    -- Unpack the sUnion membership
    rcases h_hd_in_sUnion with ⟨m', hm', hhdm'⟩
    -- By chain property, m and m' are comparable
    have hcomp := h1.total hm hm'
    -- Take the larger one (which is still in the chain)
    have h_union_in_c : m' ∪ m ∈ c := by
      cases hcomp with
      | inl hsub =>
        have : m' ∪ m = m' := Set.union_eq_left.mpr hsub
        simpa [this] using hm'
      | inr hsub =>
        have : m' ∪ m = m := Set.union_eq_right.mpr hsub
        simpa [this] using hm
    refine ⟨m' ∪ m, h_union_in_c, ?_⟩
    intro ψ hmem
    have hcons : (ψ = hd) ∨ (ψ ∈ tl) := by
      simpa [List.mem_cons] using hmem
    have : (ψ ∈ m') ∨ (ψ ∈ m) := by
      cases hcons with
      | inl hEq => subst hEq; exact Or.inl hhdm'
      | inr hψtl => exact Or.inr (htl ψ hψtl)
    simpa [Set.mem_union] using this

/--
**Lindenbaum's Lemma**: Every consistent set Γ can be extended to a maximally
consistent set Γ' ⊇ Γ.

**Proof Strategy**: Apply Zorn's lemma to the poset P of all consistent extensions of Γ,
ordered by inclusion. Show that every chain has an upper bound (its union), then Zorn
gives a maximal element, which is maximally consistent.

This is the key existence theorem that enables the canonical model construction.
-/
lemma lindenbaum (AX Γ : Ctx) (hax : ax_consist AX Γ) :
  ∃ Γ', max_ax_consist AX Γ' ∧ Γ ⊆ Γ' := by
  -- Define the poset: consistent extensions of Γ
  let P := { Γ'' | Γ'' ⊇ Γ ∧ ax_consist AX Γ''}
  -- Show every chain has an upper bound
  have h : ∀ c ⊆ P, IsChain (· ⊆ ·) c → ∃ ub ∈ P, ∀ S ∈ c, S ⊆ ub := by
    intro c h2 h3
    by_cases h4 : c.Nonempty
    · -- Non-empty chain: union is an upper bound
      use ⋃₀ c
      have h5 := lindenhelper c h4 h3
      constructor
      · constructor
        · -- ⋃₀ c ⊇ Γ
          obtain ⟨Γ'', h4⟩ := h4
          have h6 := Set.mem_of_mem_of_subset h4 h2
          obtain ⟨h6, _⟩ := h6
          apply Set.subset_sUnion_of_subset c Γ'' h6 h4
        · -- ⋃₀ c is consistent
          intro L h6
          -- Find single element containing all of L
          obtain ⟨m, h5⟩ := h5 L h6
          obtain ⟨h7, h5⟩ := h5
          obtain ⟨_, h9⟩ := (Set.mem_of_mem_of_subset h7 h2)
          apply h9
          exact h5
      · -- Every s ∈ c is a subset of ⋃₀ c
        intro S h7
        exact Set.subset_sUnion_of_mem h7
    · -- Empty chain: Γ itself is an upper bound
      use Γ
      constructor
      · constructor
        · exact Set.Subset.rfl
        · exact hax
      · intro S hs
        exfalso
        exact h4 ⟨S, hs⟩
  -- Γ is in P
  have : Γ ∈ P := by
    constructor
    · exact Set.Subset.rfl
    · exact hax
  -- Apply Zorn's lemma
  obtain ⟨Γ', hmax⟩ := zorn_subset P h
  use Γ'
  -- hmax : (Γ' ∈ P) ∧ (∀ y ∈ P, Γ' ⊆ y → y ⊆ Γ')
  obtain ⟨h_in_P, h_maximal⟩ := hmax
  constructor
  · -- Show Γ' is maximally consistent
    constructor
    · -- Γ' is consistent
      exact h_in_P.2
    · -- Γ' is maximal: any proper superset is inconsistent
      intro Γ'' hproper
      rcases hproper with ⟨hsub, hnot_sub⟩
      intro hcons
      -- If Γ'' were consistent, Zorn's maximality would force Γ'' ⊆ Γ'
      have h_eq : Γ'' = Γ' := by
        apply Set.Subset.antisymm
        · -- Γ'' ⊆ Γ' by Zorn's maximality
          apply h_maximal
          · -- Γ'' ∈ P: it extends Γ and is consistent
            constructor
            · -- Γ'' ⊇ Γ
              apply Set.Subset.trans h_in_P.1 hsub
            · -- Γ'' is consistent
              exact hcons
          · -- Γ' ⊆ Γ''
            exact hsub
        · -- Γ' ⊆ Γ'' by assumption
          exact hsub
      -- But this contradicts Γ' ⊂ Γ'' (proper subset means not equal)
      exact hnot_sub (h_eq ▸ Set.Subset.rfl)
  · -- Γ ⊆ Γ'
    exact h_in_P.1

/--
**Corollary 8 (Existence Theorem)**: Every semantically consistent axiom system
has at least one maximally consistent set.

**Proof**: The empty set ∅ is consistent (proves nothing), so by Lindenbaum
it extends to a maximal consistent set.

This existence result is crucial for the canonical model: we know there are
"enough" maximally consistent sets to Form a complete model.
-/
lemma max_ax_exists (AX : Ctx) (hax : sem_cons AX) :
  ∃ Γ : Ctx, max_ax_consist AX Γ := by
  -- Show ∅ is consistent
  have h₁ : ax_consist AX ∅ := by
    intro L hL
    -- All elements of L are in ∅, so L = []
    have hL_nil : L = [] := listempty hL (rfl : (∅ : Ctx) = ∅)
    subst hL_nil
    -- ⊤ ⊃ ⊥ is not provable in consistent systems
    by_contra hcontra
    have hImp : ProofK AX (fin_conj ([] : List Form) ⊃ Form.bot) := not_not.mp hcontra
    -- From ⊤ ⊃ ⊥ and ⊤, derive ⊥
    have hBot : ProofK AX Form.bot := mp hImp prtrue
    exact (nprfalse AX hax) hBot
  -- Apply Lindenbaum to ∅
  obtain ⟨Γ, hΓ_cons, _⟩ := lindenbaum AX ∅ h₁
  exact ⟨Γ, hΓ_cons⟩

------------------------------------------------------------------------------
-- § 6. Maximal Consistent Sets - Derived Properties
------------------------------------------------------------------------------

/-- **Helper for Exercise 1**: Technical lemma for combining derivations. -/
lemma ex1help {AX Γ : Ctx} {φ : Form} {L L' : List Form} :
  (∀ ψ ∈ L, ψ ∈ Γ) →
  ProofK AX (fin_conj L ⊃ φ) →
  (∀ ψ ∈ L', ψ ∈ Set.insert φ Γ) →
  ∃ L'' : List Form, (∀ ψ ∈ L'', ψ ∈ Γ) ∧ ProofK AX (fin_conj L'' ⊃ fin_conj L') := by
  intro hL hL_impφ hL'
  induction L' with
  | nil =>
    refine ⟨[], ?_, ?_⟩
    · intro ψ hmem; cases hmem  -- impossible: no elements in empty list
    · exact identity
  | cons hd tl ih =>
    have h_hd : hd ∈ Set.insert φ Γ := hL' hd (by simp)
    have h_tl : ∀ ψ ∈ tl, ψ ∈ Set.insert φ Γ := by
      intro ψ hmem
      exact hL' ψ (by simp [hmem])
    obtain ⟨L'', hL''_subΓ, h_imp_tail⟩ := ih h_tl
    rcases (Set.mem_insert_iff.mp h_hd) with h_eqφ | h_hd_inΓ
    · -- Case: hd = φ, use L ++ L''
      subst h_eqφ
      refine ⟨(L'' ++ L), ?_, ?_⟩
      · intro ψ hmem
        have : (ψ ∈ L'') ∨ (ψ ∈ L) := (List.mem_append).1 hmem
        cases this with
        | inl hψL'' => exact hL''_subΓ ψ hψL''
        | inr hψL   => exact hL ψ hψL
      · exact (cut (mp pl6 fin_conj_append)
              (cut (mp pl5 and_switch)
                  (imp_and_and_imp (mp (mp pl4 hL_impφ) h_imp_tail))))
    · -- Case: hd ∈ Γ, use hd :: L''
      refine ⟨(hd :: L''), ?_, ?_⟩
      · intro ψ hmem
        have : (ψ = hd) ∨ (ψ ∈ L'') := by
          simpa [List.mem_cons] using hmem
        cases this with
        | inl h_eq  => subst h_eq; exact h_hd_inΓ
        | inr hψL'' => exact hL''_subΓ ψ hψL''
      · exact imp_and_imp h_imp_tail

/--
**Exercise 1 (General Deduction)**: If a finite subset L ⊆ Γ proves φ
and Γ is maximally consistent, then φ ∈ Γ.

This is the key bridge between syntactic derivability and semantic membership.
-/
lemma exercise1 {AX Γ : Ctx} {φ : Form} {L : List Form} :
  max_ax_consist AX Γ → (∀ ψ ∈ L, ψ ∈ Γ) → ProofK AX (fin_conj L ⊃ φ) → φ ∈ Γ := by
  intro h1 h2 h3
  by_contra h4
  obtain ⟨h1, h5⟩ := h1
  -- Γ ∪ {φ} is inconsistent by maximality
  specialize h5 (Γ ∪ {φ})
  simp at h5
  specialize h5 (Set.ssubset_insert h4)
  rw [ax_consist] at h5
  push_neg at h5
  -- So there exists L' ⊆ Γ proving ⊥
  obtain ⟨L', h5⟩ := h5
  obtain ⟨h5, h6⟩ := h5
  rw [fin_ax_consist] at h6
  push_neg at h6
  -- Use ex1help to combine the derivations
  have h7 := ex1help h2 h3 h5
  obtain ⟨L'', h7⟩ := h7
  obtain ⟨h7, h8⟩ := h7
  -- L'' ⊆ Γ proves ⊥, contradicting consistency
  apply h1 L'' h7
  exact cut h8 h6

/--
**Common pattern extractor**: Derive a single formula from a single premise
in a maximally consistent set.
-/
private lemma max_derive_single {AX Γ : Ctx} {φ ψ : Form}
  (hmax : max_ax_consist AX Γ) (hφ : φ ∈ Γ) (himp : ProofK AX (φ ⊃ ψ)) : ψ ∈ Γ := by
  apply exercise1 hmax (L := [φ])
  · intro χ hmem
    rw [List.mem_singleton] at hmem
    rw [hmem]
    exact hφ
  · simp only [fin_conj]
    exact cut (mp pl5 phi_and_true) himp

-- Properties of maximally consistent sets

/-- **Double negation** holds in maximally consistent sets. -/
lemma max_dn (AX Γ : Ctx) (h : max_ax_consist AX Γ) (φ : Form) :
  (φ ∈ Γ) ↔ (∼∼φ) ∈ Γ := by
  constructor
  · intro h1
    have h2 : (∀ ψ ∈ [φ], ψ ∈ Γ) → ProofK AX (fin_conj [φ] ⊃ (∼∼φ)) → (∼∼φ) ∈ Γ :=
      exercise1 h
    apply h2
    · intro ψ hψ; simp at hψ; subst hψ; exact h1
    · exact (cut (mp pl5 phi_and_true) dni)
  · intro h1
    have h2 : (∀ ψ ∈ [∼∼φ], ψ ∈ Γ) → ProofK AX (fin_conj [∼∼φ] ⊃ φ) → φ ∈ Γ :=
      exercise1 h
    apply h2
    · intro ψ hψ; simp at hψ; subst hψ; exact h1
    · exact (cut (mp pl5 phi_and_true) dne)

/-- **Box respects double negation**: ¬□φ → ¬□¬¬φ in maximally consistent sets. -/
lemma max_boxdn (AX Γ : Ctx) (h : max_ax_consist AX Γ) (φ : Form) :
  (∼(□φ)) ∈ Γ → (∼(□(∼(∼φ)))) ∈ Γ := by
  intro h1
  have h2 : (∀ ψ ∈ [(∼(□φ))], ψ ∈ Γ) → ProofK AX (fin_conj [(∼(□φ))] ⊃ (∼(□(∼(∼φ))))) →
    (∼(□(∼(∼φ)))) ∈ Γ := exercise1 h
  apply h2
  · intro ψ hψ; simp at hψ; subst hψ; exact h1
  · exact (cut (mp pl5 phi_and_true) (mp pl5 box_dn))

/-- **Negation characterization**: φ ∉ Γ ↔ ¬φ ∈ Γ in maximally consistent sets. -/
lemma max_notiff (AX Γ : Ctx) (h : max_ax_consist AX Γ) (φ : Form) :
  (φ ∉ Γ) ↔ (∼φ) ∈ Γ := by
  have hcons : ax_consist AX Γ := max_imp_ax h
  have hdec_noboth :
      ∀ ψ, ((ψ ∈ Γ) ∨ (∼ψ) ∈ Γ) ∧ ¬(ψ ∈ Γ ∧ (∼ψ) ∈ Γ) :=
    (six AX Γ hcons).mp h
  constructor
  · -- φ ∉ Γ → ¬φ ∈ Γ
    intro hnot
    have hφ := hdec_noboth φ
    cases hφ.1 with
    | inl hφin  => exact (hnot hφin).elim
    | inr hneg  => exact hneg
  · -- ¬φ ∈ Γ → φ ∉ Γ
    intro hneg
    have hφ := hdec_noboth φ
    intro hφin
    exact (hφ.2 ⟨hφin, hneg⟩)

/-- **Implication introduction**: (φ ∈ Γ → ψ ∈ Γ) implies (φ ⊃ ψ) ∈ Γ. -/
lemma max_imp_1 {AX Γ : Ctx} {φ ψ : Form} :
  max_ax_consist AX Γ → (φ ∈ Γ → ψ ∈ Γ) → (φ ⊃ ψ) ∈ Γ := by
  intro h1 h2
  rw [imp_iff_not_or] at h2
  cases h2 with
  | inl h2 =>
    -- ¬φ ∈ Γ, so prove (φ ⊃ ψ) from ¬φ
    have h3 : (∀ χ ∈ [∼φ], χ ∈ Γ) → ProofK AX (fin_conj [∼φ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ :=
      exercise1 h1
    apply h3
    · intro χ hχ; simp at hχ; subst hχ; exact (max_notiff AX Γ h1 φ).mp h2
    · exact cut (mp pl5 phi_and_true) (and_right_imp.mp exfalso)
  | inr h2 =>
    -- ψ ∈ Γ, so prove (φ ⊃ ψ) from ψ
    have h3 : (∀ χ ∈ [ψ], χ ∈ Γ) → ProofK AX (fin_conj [ψ] ⊃ (φ ⊃ ψ)) → (φ ⊃ ψ) ∈ Γ :=
      exercise1 h1
    apply h3
    · intro χ hχ; simp at hχ; subst hχ; exact h2
    · exact (cut (mp pl5 phi_and_true) pl1)

/-- **Modus ponens**: If (φ ⊃ ψ) ∈ Γ and φ ∈ Γ, then ψ ∈ Γ. -/
lemma max_imp_2 {AX Γ : Ctx} {φ ψ : Form} :
  max_ax_consist AX Γ → (φ ⊃ ψ) ∈ Γ → φ ∈ Γ → ψ ∈ Γ := by
  intro h1 h2 h3
  have h4 : (∀ χ ∈ [φ, (φ ⊃ ψ)], χ ∈ Γ) → ProofK AX (fin_conj [φ, (φ ⊃ ψ)] ⊃ ψ) → ψ ∈ Γ :=
    exercise1 h1
  apply h4
  · intro χ h5
    cases h5 with
    | head => exact h3
    | tail _ h5 =>
      cases h5 with
      | head => exact h2
      | tail _ h5 => cases h5
  · exact and_right_imp.mpr (mp pl5 phi_and_true)

/-- **Conjunction introduction**: φ ∈ Γ ∧ ψ ∈ Γ implies (φ ∧ ψ) ∈ Γ. -/
lemma max_conj_1 {AX Γ : Ctx} {φ ψ : Form} :
  max_ax_consist AX Γ → (φ ∈ Γ ∧ ψ ∈ Γ) → (φ & ψ) ∈ Γ := by
  intro h1 h2
  have h3 : (∀ χ ∈ [φ], χ ∈ Γ) → ProofK AX (fin_conj [φ] ⊃ (ψ ⊃ (φ & ψ))) →
    (ψ ⊃ (φ & ψ)) ∈ Γ := exercise1 h1
  apply max_imp_2 h1
  · apply h3
    · intro χ hχ; simp at hχ; subst hχ; exact h2.left
    · exact (cut (mp pl5 phi_and_true) pl4)
  · exact h2.right

/-- **Left conjunction elimination**: (φ ∧ ψ) ∈ Γ implies φ ∈ Γ. -/
lemma max_conj_2 {AX Γ : Ctx} {φ ψ : Form} :
  max_ax_consist AX Γ → (φ & ψ) ∈ Γ → φ ∈ Γ := by
  intro h1 h2
  have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → ProofK AX (fin_conj [(φ & ψ)] ⊃ φ) → φ ∈ Γ :=
    exercise1 h1
  apply h3
  · intro χ hχ; simp at hχ; subst hχ; exact h2
  · exact (cut (mp pl5 phi_and_true) pl5)

/-- **Right conjunction elimination**: (φ ∧ ψ) ∈ Γ implies ψ ∈ Γ. -/
lemma max_conj_3 {AX Γ : Ctx} {φ ψ : Form} :
  max_ax_consist AX Γ → (φ & ψ) ∈ Γ → ψ ∈ Γ := by
  intro h1 h2
  have h3 : (∀ χ ∈ [(φ & ψ)], χ ∈ Γ) → ProofK AX (fin_conj [(φ & ψ)] ⊃ ψ) → ψ ∈ Γ :=
    exercise1 h1
  apply h3
  · intro χ hχ; simp at hχ; subst hχ; exact h2
  · exact (cut (mp pl5 phi_and_true) pl6)

/--
**Alternative characterization**: Maximal consistency via subset maximality.
Γ is maximal iff it's consistent and equals any consistent extension.
-/
lemma max_equiv (AX Γ : Ctx) : max_ax_consist AX Γ ↔ ax_consist AX Γ ∧
  ∀ Γ', ax_consist AX Γ' → Γ ⊆ Γ' → Γ = Γ' := by
  constructor
  · intro h1
    constructor
    · exact h1.left
    · intro Γ' h2 h3
      rw [Set.Subset.antisymm_iff]
      constructor
      · exact h3
      · by_contra h4
        exact h1.right Γ' ⟨h3, h4⟩ h2
  · intro h1
    constructor
    · exact h1.left
    · intro Γ' h2
      by_contra h3
      rw [Set.ssubset_def] at h2
      apply h2.right
      rw [h1.right Γ' h3 h2.left]

end