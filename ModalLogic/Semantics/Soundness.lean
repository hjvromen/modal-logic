/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen
Converted to Lean 4 with improvements
-/


import ModalLogic.Semantics.Correspondence

namespace Modal
open Modal
open BasicModal

/-! ## Soundness of Modal Logics

This file establishes the soundness of modal logics K, T, S4, and S5. Soundness ensures
that provability implies validity: any formula derivable in the proof system is true in
all appropriate Kripke frames.

### Mathematical Background

**Modal Logic K**: The basic modal logic with no frame constraints.
- Soundness: `⊢ φ` implies `φ` is valid in all frames

**Modal Logic T**: K + reflexivity axiom `□φ → φ`
- Soundness: `T ⊢ φ` implies `φ` is valid in all reflexive frames

**Modal Logic S4**: T + transitivity axiom `□φ → □□φ`
- Soundness: `S4 ⊢ φ` implies `φ` is valid in all reflexive-transitive frames

**Modal Logic S5**: T + Euclidean axiom `◇φ → □◇φ`
- Soundness: `S5 ⊢ φ` implies `φ` is valid in all equivalence frames

### Proof Strategy

Soundness proofs follow a uniform pattern:
1. Prove soundness by structural induction on derivations
2. Each case corresponds to an axiom or inference rule
3. Show that if premises are valid, conclusion is valid
4. For modal logics beyond K, show characteristic axioms are valid in appropriate frames

The key insight: syntactic derivability → semantic validity
- If we can prove φ (syntax), then φ must be true in all models (semantics)
- This guarantees the proof system doesn't prove false statements

### Main Results

- `soundness`: Soundness theorem for modal logic K
- `TSoundness`: Soundness theorem for modal logic T
- `S4Soundness`: Soundness theorem for modal logic S4
- `S5Soundness`: Soundness theorem for modal logic S5
- Frame class inclusion results showing the hierarchy: S5 ⊆ S4 ⊆ T ⊆ K
-/

------------------------------------------------------------------------------
-- § 1. Soundness for Modal Logic K
------------------------------------------------------------------------------

/--
**Soundness of K**: If a formula `φ` is provable from axioms `AX` in the K system,
then `φ` is a semantic consequence of `AX` in all Kripke frames.

This is the fundamental soundness theorem establishing that the proof system
doesn't prove anything false - if we can derive it, it must be true.

**Proof by structural induction** on the derivation of `ProofK AX φ`:
- Each axiom case shows the axiom is semantically valid
- Inference rules (mp, nec) preserve semantic validity
- The induction ensures the entire derivation tree is sound
-/
theorem soundness (AX : Ctx) (φ : Form) :
    ProofK AX φ → globalSemCsq AX φ := by
  intro h
  induction h with
  | hyp hmem =>
      -- Case: φ is an axiom from AX
      -- If φ ∈ AX, then by assumption all axioms hold in the model
      intro F v hAX x
      exact hAX _ x hmem

  | pl1 =>
      -- Propositional axiom 1: φ → (ψ → φ)
      -- Semantically: if φ holds at x, then regardless of whether ψ holds, φ still holds
      -- This is the K combinator from combinatory logic
      intro F v _ x _ _
      assumption

  | pl2 =>
      -- Propositional axiom 2: (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))
      -- Semantically: distribution of implication
      -- This is the S combinator from combinatory logic
      -- Given: φ → (ψ → χ), and φ → ψ, and φ
      -- We need to show: χ
      intro F v _ x hφψχ hφψ hφ
      exact hφψχ hφ (hφψ hφ)

  | pl3 =>
      -- Propositional axiom 3 (contraposition): ((¬φ → ¬ψ) → (ψ → φ))
      -- If ¬φ implies ¬ψ, then ψ implies φ (by contraposition)
      intro F v _ x hNotφImplNotψ hψ
      by_contra hNotφ
      have hNotψ : forces F v x (¬ₘ _) := hNotφImplNotψ hNotφ
      exact hNotψ hψ

  | pl4 =>
      -- Conjunction introduction: φ → (ψ → φ ∧ ψ)
      -- If both φ and ψ hold, then their conjunction holds
      intro F v _ x hφ hψ
      exact ⟨hφ, hψ⟩

  | pl5 =>
      -- Conjunction elimination (left): φ ∧ ψ → φ
      -- If a conjunction holds, its left conjunct holds
      intro F v _ x h
      exact h.1

  | pl6 =>
      -- Conjunction elimination (right): φ ∧ ψ → ψ
      -- If a conjunction holds, its right conjunct holds
      intro F v _ x h
      exact h.2

  | kdist =>
      -- **K axiom** (distribution): □(φ → ψ) → (□φ → □ψ)
      -- This is the characteristic axiom of modal logic
      -- Semantically: necessity distributes over implication
      -- If (φ → ψ) holds at all accessible worlds, and φ holds at all accessible worlds,
      -- then ψ holds at all accessible worlds
      intro F v _ x hBoxImpl hBoxφ y hxy
      exact hBoxImpl y hxy (hBoxφ y hxy)

  | nec _ ih =>
      -- **Necessitation rule**: if ⊢ φ then ⊢ □φ
      -- This is the only modal inference rule
      -- Semantically: if φ is valid (true at all worlds), then □φ is valid
      -- For any accessible world y, φ holds at y (by IH), so □φ holds at x
      intro F v hAX x y _
      exact ih F v hAX y

  | mp _ _ ih_hpq ih_hp =>
      -- **Modus ponens**: from φ and φ → ψ, derive ψ
      -- This is the fundamental inference rule of logic
      -- By IH, both φ and (φ → ψ) hold at x, so ψ holds at x
      intro F v hAX x
      exact ih_hpq F v hAX x (ih_hp F v hAX x)

------------------------------------------------------------------------------
-- § 2. Helper Lemmas for Frame-Specific Soundness
------------------------------------------------------------------------------

/--
**Soundness relative to frame classes**: If `φ` is provable from axioms `Γ`,
and all axioms in `Γ` are valid in frame class `C`, then `φ` is valid in `C`.

This lemma is the key to proving soundness for specific modal logics by
showing their characteristic axioms are valid in the appropriate frame class.

**Strategy**:
1. Assume all axioms in Γ are valid in frame class C
2. Prove by induction that φ is valid in C
3. This reduces soundness of T/S4/S5 to showing their axioms are valid

This is a "relativized" version of the soundness theorem that works for
arbitrary frame classes, not just all frames.
-/
lemma soundnessHelper {Γ : Ctx} {φ : Form} {C : Set Frame.{0}} :
    ProofK Γ φ → (∀ ψ ∈ Γ, FValid ψ C) → FValid φ C := by
  intros h hΓ F hF v
  -- The proof mirrors the soundness theorem, but restricted to frames in C
  induction h with
  | hyp hψ =>
      -- Axiom case: use the assumption that all axioms are valid in C
      intro x
      exact hΓ _ hψ F hF v x
  | pl1 => aesop
  | pl2 => aesop
  | pl3 =>
      intros x hNotφImplNotψ hψ
      by_contra hNotφ
      have hNotψ : forces F v x (¬ₘ _) := hNotφImplNotψ hNotφ
      exact hNotψ hψ
  | pl4 =>
      intros x hφ hψ
      exact ⟨hφ, hψ⟩
  | pl5 =>
      intros x h
      exact h.1
  | pl6 =>
      intros x h
      exact h.2
  | kdist => aesop
      -- K axiom is valid in any frame
  | nec _ ih => aesop
      -- Necessitation preserves validity in frame class C
  | mp _ _ ih_hpq ih_hp =>
      -- Modus ponens preserves validity
      intro x
      exact ih_hpq x (ih_hp x)

/--
**Monotonicity of validity**: If `C ⊆ C'` and `φ` is valid in `C'`,
then `φ` is valid in `C`.

This captures the intuition that imposing more constraints on frames
can only make it easier for a formula to be valid.

**Example**: If φ is valid in all frames, then it's valid in reflexive frames
(since reflexive frames are a subset of all frames).

This lemma is crucial for establishing the frame class hierarchy:
S5 ⊆ S4 ⊆ T ⊆ K
-/
lemma validMonotone {C C' : Set Frame.{0}} {φ : Form} :
    C ⊆ C' → FValid φ C' → FValid φ C := by
  intros hSub hValid F hFC v x
  exact hValid F (hSub hFC) v x

------------------------------------------------------------------------------
-- § 3. Axiom Systems for T, S4, and S5
------------------------------------------------------------------------------

-- Note: TAxioms, S4Axioms, and S5Axioms are defined in ProofSystem.lean
-- They are imported through the chain: soundness → Correspondence → semantics → syntax

------------------------------------------------------------------------------
-- § 4. Soundness for T, S4, and S5
------------------------------------------------------------------------------

/--
All T axioms (`□φ → φ`) are valid in reflexive frames.

**Proof idea**: In a reflexive frame, if `□φ` holds at `x`, then `φ` holds at all
accessible worlds. By reflexivity, `x` is accessible from itself, so `φ` holds at `x`.

This is the semantic justification for the T axiom: necessity implies actuality
when we can "see" our own world.
-/
lemma TAxiomsValid : ∀ φ ∈ TAxioms, FValid φ refClass := by
  intros φ hφ
  obtain ⟨ψ, rfl⟩ := hφ
  intro F hRef v x hBox
  -- hRef : ∀ (x : F.states), F.rel x x  (reflexivity)
  -- From □ψ, we know ψ holds at all accessible worlds
  -- By reflexivity, x is accessible from x (hRef x), so ψ holds at x
  exact hBox x (hRef x)

/--
**Soundness of T**: If `φ` is provable in T, then `φ` is valid in all reflexive frames.

This theorem establishes that the T proof system is sound for reasoning about
reflexive accessibility relations. Everything provable in T is true in reflexive frames.
-/
theorem TSoundness (φ : Form) :
    ProofK TAxioms φ → FValid φ refClass := fun h =>
  soundnessHelper h TAxiomsValid

/--
All S4 axioms are valid in reflexive-transitive frames.

**Two axiom groups**:
1. T axiom (□ψ → ψ): valid by reflexivity
2. 4 axiom (□ψ → □□ψ): valid by transitivity

**Transitivity argument**:
- Suppose □ψ holds at x (ψ holds at all worlds accessible from x)
- Let y be accessible from x
- We need to show □ψ holds at y, i.e., ψ holds at all worlds accessible from y
- Let z be accessible from y
- By transitivity, z is accessible from x
- Therefore ψ holds at z (from our initial assumption)
- So □ψ holds at y
-/
lemma S4AxiomsValid : ∀ φ ∈ S4Axioms, FValid φ refTransClass := by
  intros φ hφ F hF v x
  obtain ⟨hRef, hTrans⟩ := hF
  cases hφ with
  | inl hT =>
      -- T axiom: □ψ → ψ (valid by reflexivity)
      obtain ⟨ψ, rfl⟩ := hT
      intro hBox
      exact hBox x (hRef x)
  | inr h4 =>
      -- 4 axiom: □ψ → □□ψ (valid by transitivity)
      -- Strategy: If ψ holds at all worlds accessible from x,
      -- and y is accessible from x, then for any z accessible from y,
      -- we have z accessible from x (by transitivity), so ψ holds at z
      obtain ⟨ψ, rfl⟩ := h4
      intro hBox y hxy z hyz
      -- hxy : x sees y, hyz : y sees z
      -- By transitivity: x sees z
      -- From hBox: ψ holds at all worlds seen by x
      -- Therefore: ψ holds at z
      exact hBox z (hTrans hxy hyz)

/--
**Soundness of S4**: If `φ` is provable in S4, then `φ` is valid in all
reflexive-transitive frames.

S4 is the modal logic of reflexive and transitive relations, often used
for reasoning about knowledge and provability.
-/
theorem S4Soundness (φ : Form) :
    ProofK S4Axioms φ → FValid φ refTransClass := fun h =>
  soundnessHelper h S4AxiomsValid

/--
All S5 axioms are valid in equivalence frames (reflexive, symmetric, transitive).

**Two axiom groups**:
1. T axiom (□ψ → ψ): valid by reflexivity
2. 5 axiom (◇ψ → □◇ψ): valid by symmetry + transitivity

**Euclidean axiom argument**:
The 5 axiom is ◇ψ → □◇ψ, which in our encoding is:
  ¬□¬ψ → □(¬□¬ψ)

Strategy for proving ◇ψ → □◇ψ:
- Assume ◇ψ holds at x (there exists an accessible world where ψ holds)
- Let z be any world accessible from x
- We need to show ◇ψ holds at z (there exists a world accessible from z where ψ holds)
- Proof by contradiction: assume □¬ψ holds at z (ψ fails at all worlds accessible from z)
- We'll derive □¬ψ at x, contradicting our assumption

The key insight: in an equivalence relation, if x sees z, then z sees x (symmetry),
so anything forced at z "propagates back" to x.
-/
lemma S5AxiomsValid : ∀ φ ∈ S5Axioms, FValid φ equivClass := by
  intros φ hφ F hF v x
  obtain ⟨hRef, hSym, hTrans⟩ := hF
  cases hφ with
  | inl hT =>
      -- T axiom: □ψ → ψ (valid by reflexivity)
      obtain ⟨ψ, rfl⟩ := hT
      intro hBox
      exact hBox x (hRef x)
  | inr h5 =>
      -- 5 axiom: ◇ψ → □◇ψ
      -- In our encoding: ¬□¬ψ → □(¬□¬ψ)
      obtain ⟨ψ, rfl⟩ := h5
      intro hDia z hxz hBoxNotPsiAtZ
      -- hDia : ◇ψ holds at x, i.e., (□¬ψ at x) → False
      -- Need to prove: ◇ψ holds at z, i.e., (□¬ψ at z) → False
      -- We have: hBoxNotPsiAtZ : □¬ψ at z

      -- Strategy: derive □¬ψ at x to contradict hDia
      apply hDia
      -- Need to prove: □¬ψ at x, i.e., ∀y accessible from x, ¬ψ at y
      intro y hxy hψAtY
      -- Given: hxy : x sees y, hψAtY : ψ at y
      -- Need to derive: contradiction

      -- From hBoxNotPsiAtZ, we know ¬ψ holds at all worlds accessible from z
      -- We need to show y is accessible from z
      -- We have: x sees z (hxz), so by symmetry z sees x (hSym hxz)
      -- We have: x sees y (hxy)
      -- By transitivity: z sees y
      have hzy : F.rel z y := hTrans (hSym hxz) hxy
      -- Now apply hBoxNotPsiAtZ to get ¬ψ at y
      have hNotPsiAtY : forces F v y (¬ₘψ) := hBoxNotPsiAtZ y hzy
      -- We have both ψ and ¬ψ at y - contradiction!
      exact hNotPsiAtY hψAtY

/--
**Soundness of S5**: If `φ` is provable in S5, then `φ` is valid in all
equivalence frames.

S5 is the modal logic of equivalence relations, often used for reasoning about
knowledge in multi-agent systems where all agents have perfect information.
-/
theorem S5Soundness (φ : Form) :
    ProofK S5Axioms φ → FValid φ equivClass := fun h =>
  soundnessHelper h S5AxiomsValid

------------------------------------------------------------------------------
-- § 5. Soundness for KD and KB
------------------------------------------------------------------------------

/--
All KD axioms (`□φ → ◇φ`) are valid in serial frames.

**Proof idea**: In a serial frame, every world has at least one successor.
If `□φ` holds at `x`, then `φ` holds at all accessible worlds.
By seriality, there exists some accessible world `y`, so `φ` holds at `y`,
witnessing `◇φ` at `x`.
-/
lemma KDAxiomsValid : ∀ φ ∈ KDAxioms, FValid φ serialClass := by
  intros φ hφ
  obtain ⟨ψ, rfl⟩ := hφ
  intro F hSerial v x hBox
  -- hSerial : ∀ x, ∃ y, F.rel x y (seriality)
  -- hBox : ∀ y, F.rel x y → forces F v y ψ
  -- Need to show ◇ψ at x, i.e., ∃ y, F.rel x y ∧ forces F v y ψ
  simp [forces, dia, neg]
  obtain ⟨y, hxy⟩ := hSerial x
  exact ⟨y, hxy, hBox y hxy⟩

/--
**Soundness of KD**: If `φ` is provable in KD, then `φ` is valid in all serial frames.

KD is the modal logic of serial relations, used in deontic logic where
the seriality condition ensures that obligations are always consistent
(there is always an ideal world to aim for).
-/
theorem KDSoundness (φ : Form) :
    ProofK KDAxioms φ → FValid φ serialClass := fun h =>
  soundnessHelper h KDAxiomsValid

/--
All KB axioms (`φ → □◇φ`) are valid in symmetric frames.

**Proof idea**: In a symmetric frame, if `φ` holds at `x` and `y` is accessible
from `x`, then by symmetry `x` is accessible from `y`, so `x` witnesses `◇φ`
at `y`. Therefore `□◇φ` holds at `x`.
-/
lemma KBAxiomsValid : ∀ φ ∈ KBAxioms, FValid φ symmClass := by
  intros φ hφ
  obtain ⟨ψ, rfl⟩ := hφ
  intro F hSymm v x hψ y hxy
  -- hSymm : Symmetric F.rel
  -- hψ : forces F v x ψ
  -- Need to show ◇ψ at y, i.e., ∃ z, F.rel y z ∧ forces F v z ψ
  simp [forces, dia, neg]
  exact ⟨x, hSymm hxy, hψ⟩

/--
**Soundness of KB**: If `φ` is provable in KB, then `φ` is valid in all symmetric frames.

KB is the modal logic of symmetric relations.
-/
theorem KBSoundness (φ : Form) :
    ProofK KBAxioms φ → FValid φ symmClass := fun h =>
  soundnessHelper h KBAxiomsValid

------------------------------------------------------------------------------
-- § 5b. Soundness for K4, KTB, KB4
------------------------------------------------------------------------------

/--
All K4 axioms (`□φ → □□φ`) are valid in transitive frames.
-/
lemma K4AxiomsValid : ∀ φ ∈ K4Axioms, FValid φ transClass := by
  intros φ hφ
  obtain ⟨ψ, rfl⟩ := hφ
  intro F hTrans v x hBox y hxy z hyz
  exact hBox z (hTrans hxy hyz)

/--
**Soundness of K4**: If `φ` is provable in K4, then `φ` is valid in all transitive frames.
-/
theorem K4Soundness (φ : Form) :
    ProofK K4Axioms φ → FValid φ transClass := fun h =>
  soundnessHelper h K4AxiomsValid

/--
All KTB axioms (T + B) are valid in reflexive-symmetric frames.
-/
lemma KTBAxiomsValid : ∀ φ ∈ KTBAxioms, FValid φ refSymmClass := by
  intros φ hφ F hF v x
  obtain ⟨hRef, hSymm⟩ := hF
  cases hφ with
  | inl hT =>
      obtain ⟨ψ, rfl⟩ := hT
      intro hBox
      exact hBox x (hRef x)
  | inr hB =>
      obtain ⟨ψ, rfl⟩ := hB
      intro hψ y hxy
      simp [forces, dia, neg]
      exact ⟨x, hSymm hxy, hψ⟩

/--
**Soundness of KTB**: If `φ` is provable in KTB, then `φ` is valid in all
reflexive-symmetric frames.
-/
theorem KTBSoundness (φ : Form) :
    ProofK KTBAxioms φ → FValid φ refSymmClass := fun h =>
  soundnessHelper h KTBAxiomsValid

/--
All KB4 axioms (B + 4) are valid in symmetric-transitive frames.
-/
lemma KB4AxiomsValid : ∀ φ ∈ KB4Axioms, FValid φ symmTransClass := by
  intros φ hφ F hF v x
  obtain ⟨hSymm, hTrans⟩ := hF
  cases hφ with
  | inl hB =>
      obtain ⟨ψ, rfl⟩ := hB
      intro hψ y hxy
      simp [forces, dia, neg]
      exact ⟨x, hSymm hxy, hψ⟩
  | inr h4 =>
      obtain ⟨ψ, rfl⟩ := h4
      intro hBox y hxy z hyz
      exact hBox z (hTrans hxy hyz)

/--
**Soundness of KB4**: If `φ` is provable in KB4, then `φ` is valid in all
symmetric-transitive frames.
-/
theorem KB4Soundness (φ : Form) :
    ProofK KB4Axioms φ → FValid φ symmTransClass := fun h =>
  soundnessHelper h KB4AxiomsValid

------------------------------------------------------------------------------
-- § 6. Frame Class Hierarchy
------------------------------------------------------------------------------

/--
**T is included in S4**: Any formula valid in all reflexive frames
is also valid in all reflexive-transitive frames.

This follows because every reflexive-transitive frame is reflexive.

**Consequence**: Every theorem of T is a theorem of S4.
The hierarchy means S4 is "stronger" than T (proves more formulas).
-/
lemma T_included_in_S4 : ∀ φ, FValid φ refClass → FValid φ refTransClass := by
  intro φ
  apply validMonotone
  -- Need to show: refTransClass ⊆ refClass
  -- Every reflexive-transitive frame is reflexive
  intro F ⟨hRef, _⟩
  exact hRef

/--
**T is included in S5**: Any formula valid in all reflexive frames
is also valid in all equivalence frames.

Every equivalence relation is reflexive (among other properties).
-/
lemma T_included_in_S5 : ∀ φ, FValid φ refClass → FValid φ equivClass := by
  intro φ
  apply validMonotone
  intro F hEquiv
  -- hEquiv : Equivalence F.rel
  -- An equivalence relation is reflexive
  exact hEquiv.refl

/--
**S4 is included in S5**: Any formula valid in all reflexive-transitive frames
is also valid in all equivalence frames.

This follows because every equivalence relation is reflexive and transitive
(it's also symmetric, but we don't need that here).

**Consequence**: The modal logic hierarchy is: S5 ⊆ S4 ⊆ T ⊆ K
Each logic is a conservative extension of the previous one.
-/
lemma S4_included_in_S5 : ∀ φ, FValid φ refTransClass → FValid φ equivClass := by
  intro φ
  apply validMonotone
  intro F hEquiv
  simp [refTransClass]
  exact ⟨hEquiv.refl, fun _ _ _ => hEquiv.trans⟩

/--
**The frame class hierarchy**: S5 ⊆ S4 ⊆ T ⊆ K

This formalizes the inclusions between modal logics:
- Every equivalence relation is reflexive and transitive
- Every reflexive-transitive relation is reflexive
- Every reflexive relation is a relation

**Philosophical significance**:
- K: no constraints (basic modal reasoning)
- T: reflexivity (necessity implies truth)
- S4: + transitivity (iterated knowledge collapses)
- S5: + symmetry (perfect information/knowledge)

Each level adds more structure, making more formulas valid.
-/
lemma frameClassHierarchy :
    equivClass ⊆ refTransClass ∧ refTransClass ⊆ refClass := by
  constructor
  · -- equivClass ⊆ refTransClass
    intro F hEquiv
    -- hEquiv : Equivalence F.rel
    simp only [refTransClass]
    constructor
    · -- Reflexive F.rel
      exact hEquiv.refl
    · -- Transitive F.rel
      intro x y z hxy hyz
      exact hEquiv.trans hxy hyz
  · -- refTransClass ⊆ refClass
    intro F ⟨hRef, _⟩
    exact hRef


------------------------------------------------------------------------------
-- § 7. Soundness for K5, KD5, and KD45
------------------------------------------------------------------------------

/--
All K5 axioms (◇φ → □◇φ) are valid in Euclidean frames.
-/
lemma K5AxiomsValid : ∀ φ ∈ K5Axioms, FValid φ euclidClass := by
  intros φ hφ
  obtain ⟨ψ, rfl⟩ := hφ
  intro F hF v x
  exact euclidHelper ψ F hF v x

/--
**Soundness of K5**: If φ is provable in K5, then φ is valid in all Euclidean frames.
-/
theorem K5Soundness (φ : Form) :
    ProofK K5Axioms φ → FValid φ euclidClass := fun h =>
  soundnessHelper h K5AxiomsValid

/--
All KD5 axioms (D + 5) are valid in serial Euclidean frames.
-/
abbrev serialEuclidClass : Set Frame.{0} := serialClass ∩ euclidClass

lemma KD5AxiomsValid : ∀ φ ∈ KD5Axioms, FValid φ serialEuclidClass := by
  intros φ hφ F hF v x
  obtain ⟨hSerial, hEuclid⟩ := hF
  cases hφ with
  | inl hD =>
    obtain ⟨ψ, rfl⟩ := hD
    exact serialHelper ψ F hSerial v x
  | inr h5 =>
    obtain ⟨ψ, rfl⟩ := h5
    exact euclidHelper ψ F hEuclid v x

/--
**Soundness of KD5**: If φ is provable in KD5, then φ is valid in all
serial Euclidean frames.
-/
theorem KD5Soundness (φ : Form) :
    ProofK KD5Axioms φ → FValid φ serialEuclidClass := fun h =>
  soundnessHelper h KD5AxiomsValid

/--
All KD45 axioms (D + 4 + 5) are valid in serial transitive Euclidean frames.
-/
abbrev serialTransEuclidClass : Set Frame.{0} := serialClass ∩ transClass ∩ euclidClass

lemma KD45AxiomsValid : ∀ φ ∈ KD45Axioms, FValid φ serialTransEuclidClass := by
  intros φ hφ F hF v x
  obtain ⟨⟨hSerial, hTrans⟩, hEuclid⟩ := hF
  rcases hφ with (hD | h4) | h5
  · obtain ⟨ψ, rfl⟩ := hD
    exact serialHelper ψ F hSerial v x
  · obtain ⟨ψ, rfl⟩ := h4
    exact transHelper ψ F hTrans v x
  · obtain ⟨ψ, rfl⟩ := h5
    exact euclidHelper ψ F hEuclid v x

/--
**Soundness of KD45**: If φ is provable in KD45, then φ is valid in all
serial transitive Euclidean frames.
-/
theorem KD45Soundness (φ : Form) :
    ProofK KD45Axioms φ → FValid φ serialTransEuclidClass := fun h =>
  soundnessHelper h KD45AxiomsValid

------------------------------------------------------------------------------
-- § 8. Soundness for KDB, KD4, K45, KB5
------------------------------------------------------------------------------

/--
All KDB axioms (D + B) are valid in serial symmetric frames.
-/
lemma KDBAxiomsValid : ∀ φ ∈ KDBAxioms, FValid φ serialSymmClass := by
  intros φ hφ F hF v x
  obtain ⟨hSerial, hSymm⟩ := hF
  cases hφ with
  | inl hD =>
    obtain ⟨ψ, rfl⟩ := hD
    exact serialHelper ψ F hSerial v x
  | inr hB =>
    obtain ⟨ψ, rfl⟩ := hB
    exact symmHelper ψ F hSymm v x

/--
**Soundness of KDB**: If φ is provable in KDB, then φ is valid in all
serial symmetric frames.
-/
theorem KDBSoundness (φ : Form) :
    ProofK KDBAxioms φ → FValid φ serialSymmClass := fun h =>
  soundnessHelper h KDBAxiomsValid

/--
All KD4 axioms (D + 4) are valid in serial transitive frames.
-/
lemma KD4AxiomsValid : ∀ φ ∈ KD4Axioms, FValid φ serialTransClass := by
  intros φ hφ F hF v x
  obtain ⟨hSerial, hTrans⟩ := hF
  cases hφ with
  | inl hD =>
    obtain ⟨ψ, rfl⟩ := hD
    exact serialHelper ψ F hSerial v x
  | inr h4 =>
    obtain ⟨ψ, rfl⟩ := h4
    exact transHelper ψ F hTrans v x

/--
**Soundness of KD4**: If φ is provable in KD4, then φ is valid in all
serial transitive frames.
-/
theorem KD4Soundness (φ : Form) :
    ProofK KD4Axioms φ → FValid φ serialTransClass := fun h =>
  soundnessHelper h KD4AxiomsValid

/--
All K45 axioms (4 + 5) are valid in transitive Euclidean frames.
-/
lemma K45AxiomsValid : ∀ φ ∈ K45Axioms, FValid φ transEuclidClass := by
  intros φ hφ F hF v x
  obtain ⟨hTrans, hEuclid⟩ := hF
  cases hφ with
  | inl h4 =>
    obtain ⟨ψ, rfl⟩ := h4
    exact transHelper ψ F hTrans v x
  | inr h5 =>
    obtain ⟨ψ, rfl⟩ := h5
    exact euclidHelper ψ F hEuclid v x

/--
**Soundness of K45**: If φ is provable in K45, then φ is valid in all
transitive Euclidean frames.
-/
theorem K45Soundness (φ : Form) :
    ProofK K45Axioms φ → FValid φ transEuclidClass := fun h =>
  soundnessHelper h K45AxiomsValid

/--
All KB5 axioms (B + 5) are valid in symmetric Euclidean frames.
-/
lemma KB5AxiomsValid : ∀ φ ∈ KB5Axioms, FValid φ symmEuclidClass := by
  intros φ hφ F hF v x
  obtain ⟨hSymm, hEuclid⟩ := hF
  cases hφ with
  | inl hB =>
    obtain ⟨ψ, rfl⟩ := hB
    exact symmHelper ψ F hSymm v x
  | inr h5 =>
    obtain ⟨ψ, rfl⟩ := h5
    exact euclidHelper ψ F hEuclid v x

/--
**Soundness of KB5**: If φ is provable in KB5, then φ is valid in all
symmetric Euclidean frames.
-/
theorem KB5Soundness (φ : Form) :
    ProofK KB5Axioms φ → FValid φ symmEuclidClass := fun h =>
  soundnessHelper h KB5AxiomsValid

end Modal
