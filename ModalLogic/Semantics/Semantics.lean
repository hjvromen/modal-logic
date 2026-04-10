import ModalLogic.Syntax.SyntaxLemmas
import Mathlib.Data.Set.Basic

/-
Semantics for the basic modal language (Kripke frames and forcing).
This version avoids any global `open Classical`, using `by classical` locally only.

This file establishes the semantic foundation for modal logic through Kripke semantics,
the standard mathematical framework for interpreting modal formulas.
-/



namespace Modal
open Modal
open BasicModal

/-!
# Kripke Semantics for Modal Logic

This file develops the semantic interpretation of modal logic through Kripke semantics,
introduced by Saul Kripke in the 1960s and now the standard framework for modal logic.

## Philosophical Motivation

**The Problem**: What do modal operators □ (necessity) and ◇ (possibility) mean?

**Kripke's Answer**: Interpret formulas not at a single "state of affairs" but at
points in a relational structure:
- States (worlds): possible configurations or situations
- Accessibility relation: which worlds are "possible alternatives" to which
- □φ is true at w: φ is true at all accessible worlds
- ◇φ is true at w: φ is true at some accessible world

This gives a precise mathematical semantics to modal reasoning.

## Core Concepts

**Frame**: A directed graph (states + accessibility relation)
  - Models the "space of possibilities"
  - Different frame properties give different modal logics (K, T, S4, S5)

**Model**: Frame + valuation (which atomic propositions hold where)
  - Gives truth values to all formulas at all worlds

**Forcing relation**: When a formula is true at a world
  - Defined recursively on formula structure
  - The key innovation: □φ quantifies over accessible worlds

## Design Choices

**Why this formalization?**
1. **Compositionality**: Truth is defined by structural recursion
2. **Modularity**: Frames separate from valuations
3. **Generality**: Works for any logic (K, T, S4, S5, etc.)
4. **Computability**: Definitions are constructive where possible

**Classical logic**: We avoid global `open Classical` but use it locally where needed
(particularly for diamond/possibility semantics involving existentials).

## Applications

- Epistemic logic: states = knowledge states, □ = "agent knows"
- Temporal logic: states = time points, R = "before" relation
- Deontic logic: states = normative situations, □ = "obligatory"
- Program logic: states = program states, R = transition relation

## Main Results

This file establishes:
- The forcing relation (truth definition)
- Multiple notions of validity (model, frame, class, universal)
- Weakening/monotonicity properties
- Semantic operations (restriction, generated subframes, products)
- Truth preservation theorems

These are the semantic foundations for soundness and completeness proofs.
-/

------------------------------------------------------------------------------
-- § 1. Kripke Frames and Models
------------------------------------------------------------------------------

/--
**Kripke frame**: The "skeleton" of modal semantics.

A frame consists of:
- `states`: A type of possible worlds/states/points
- `rel`: An accessibility relation between states

**Intuition**: Think of a frame as a directed graph where:
- Nodes are states (possible worlds)
- Edges are the accessibility relation

**Examples**:
- Reflexive frame: every world sees itself (models logic T)
- Transitive frame: if w₁ sees w₂ and w₂ sees w₃, then w₁ sees w₃ (models logic S4)
- Equivalence relation: partition into clusters (models logic S5)

**Frame properties determine modal logic**:
- Different properties of `rel` correspond to different modal axioms
- This is the content of correspondence theory (see Correspondence.lean)

**Why separate frames from models?**
Frames capture the "structural" part of semantics (independent of atomic propositions).
This allows us to study frame classes (reflexive frames, transitive frames, etc.)
separately from specific interpretations.

**Universe polymorphism**: The `states` field is `Type*`, making `Frame` itself
universe-polymorphic. Core operations (`forces`, `fValid`, `mValid`, etc.) are
polymorphic in the frame's universe, so they can be reused with frames at any
universe level. Definitions that quantify over *all* frames (`uValid`,
`globalSemCsq`, `FValid`, frame class sets) are pinned to `Frame.{0}` because
Lean requires an explicit universe when the binder ranges over all frames in a
given universe.
-/
structure Frame where
  /-- The type of possible worlds. Universe-polymorphic (`Type*`) so that
      the same `Frame` definition works at any universe level, enabling
      reuse across syntactic semantics, epistemic modules, and downstream
      libraries that may place states in higher universes. -/
  states : Type*
  /-- The accessibility relation between worlds. -/
  rel    : states → states → Prop

/--
**Kripke model**: A frame plus an interpretation of atomic propositions.

A model adds to a frame:
- `v`: A valuation function that says which atomic propositions are true at which states

**Type of v**: `Nat → f.states → Prop`
- For each variable number n and state x
- Returns whether variable n is true at state x

**Why this type?**
- Variables are represented by natural numbers (from syntax.lean)
- We need to assign truth values to variables at each state
- Different states can have different atomic truths

**Philosophical interpretation**:
- Frames give the "modal structure" (what's possible)
- Valuations give the "factual content" (what's actually true)
- Together they determine truth of all formulas

**Example**: In epistemic logic:
- States might be different "information states" of an agent
- Valuation tells us which basic facts the agent knows in each state
- Accessibility relates states the agent can't distinguish
-/
structure Model where
  f : Frame
  v : Nat → f.states → Prop

------------------------------------------------------------------------------
-- § 2. The Forcing Relation (Truth at a World)
------------------------------------------------------------------------------

/--
**Kripke forcing relation**: The recursive definition of truth at a world.

`forces F v x φ` means: formula φ is true at state x in the model (F, v).

**Recursive clauses** (by formula structure):

1. **Bottom (⊥)**: Always false
   - `forces F v x ⊥ := False`

2. **Variables (p)**: True iff the valuation says so
   - `forces F v x (var n) := v n x`

3. **Conjunction (φ ∧ ψ)**: Both must be true
   - `forces F v x (φ ∧ ψ) := forces F v x φ ∧ forces F v x ψ`

4. **Implication (φ → ψ)**: Standard logical implication
   - `forces F v x (φ → ψ) := forces F v x φ → forces F v x ψ`

5. **Box (□φ)**: Must be true at ALL accessible worlds
   - `forces F v x (□φ) := ∀y. F.rel x y → forces F v y φ`
   - **This is the key modal clause!**

**Derived operators**:
- Negation: `forces F v x (¬φ) ↔ ¬(forces F v x φ)`
- Diamond: `forces F v x (◇φ) ↔ ∃y. F.rel x y ∧ forces F v y φ`

**Why this definition?**
- **Compositional**: Truth of compounds depends only on truth of parts
- **Local**: Truth at x only depends on x and its accessible worlds
- **Structural**: Mirrors the structure of formulas
- **Intuitive**: Matches informal understanding of modality

**Philosophical meaning of □**:
- Necessity: □φ means "φ holds in all relevant possibilities"
- Knowledge: □φ means "agent knows φ" (true in all epistemically possible worlds)
- Always: □φ means "φ holds at all future times"
- Obligation: □φ means "φ is obligatory" (true in all ideal worlds)

The meaning depends on how we interpret the accessibility relation!
-/
def forces (F : Frame) (v : Nat → F.states → Prop) :
    F.states → Form → Prop
  | _, Form.bot        => False
  | x, Form.var n      => v n x
  | x, Form.and φ ψ    => forces F v x φ ∧ forces F v x ψ
  | x, Form.impl φ ψ   => forces F v x φ → forces F v x ψ
  | x, Form.box φ      => ∀ y, F.rel x y → forces F v y φ

------------------------------------------------------------------------------
-- § 3. Notions of Validity
------------------------------------------------------------------------------

/--
**Model validity**: True at all states in a specific model.

`mValid φ F v` means: φ is true at every state in the model (F, v).

**Note**: This fixes both the frame F and the valuation v.

**Intuition**: The formula is "universally true" in this specific model.
Not used as often as frame validity in modal logic, but important for completeness proofs.
-/
def mValid (φ : Form) (F : Frame) (v : Nat → F.states → Prop) : Prop :=
  ∀ x, forces F v x φ

/--
**Frame validity** (per-frame validity): True in all models on a frame.

`fValid φ F` means: for every valuation v and every state x, φ is true at x.

**This is the most important validity notion** for correspondence theory!

**Key property**: Frame validity depends only on the frame structure, not on any
particular valuation. This allows us to connect modal axioms to frame properties.

**Examples**:
- `fValid (□p → p) F` iff F is reflexive
- `fValid (□p → □□p) F` iff F is transitive
- These are the correspondence theorems (see Correspondence.lean)

**Why universal quantification over v?**
We want formulas that are true "no matter what the atomic facts are" -
only the modal structure matters.
-/
def fValid (φ : Form) (F : Frame) : Prop :=
  ∀ v x, forces F v x φ

/--
**Frame class validity**: True in all frames in a class.

`FValid φ 𝔉` means: φ is valid in every frame in the class 𝔉.

**Applications**:
- `FValid φ refClass`: φ is valid in all reflexive frames
- `FValid φ transClass`: φ is valid in all transitive frames
- `FValid φ equivClass`: φ is valid in all equivalence frames

**Connection to modal logics**:
- Logic K: valid in all frames (universal validity)
- Logic T: valid in reflexive frames
- Logic S4: valid in reflexive-transitive frames
- Logic S5: valid in equivalence frames

This notion is crucial for soundness theorems: proving that modal axioms
are semantically valid in their corresponding frame classes.
-/
def FValid (φ : Form) (𝔉 : Set Frame.{0}) : Prop :=
  ∀ F ∈ 𝔉, ∀ v x, forces F v x φ

/--
**Universal validity** (validity in all frames): The strongest notion.

`uValid φ` means: φ is valid in every frame, with every valuation, at every state.

**Equivalently**: φ is a theorem of the minimal modal logic K.

**Examples of universally valid formulas**:
- All tautologies: `p → p`, `p → (q → p)`, etc.
- K axiom: `□(p → q) → (□p → □q)`
- All theorems of modal logic K

**Not universally valid** (but valid in some frame classes):
- T axiom: `□p → p` (requires reflexivity)
- 4 axiom: `□p → □□p` (requires transitivity)

**Philosophical note**: Universal validity = "true in all possible worlds in all
possible models" - the absolute strongest Form of truth.
-/
def uValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}) v x, forces F v x φ

/--
**Context forcing**: All formulas in Γ are true at all states.

`forcesCtx F v Γ` means: for every φ ∈ Γ and every state x, φ is true at x.

**Usage**: This represents assumptions/hypotheses in semantic consequence.

**Intuition**: The context Γ is the set of "background assumptions" that we're
taking to be true throughout the model.
-/
def forcesCtx (F : Frame) (v : Nat → F.states → Prop) (Γ : Ctx) : Prop :=
  ∀ φ x, φ ∈ Γ → forces F v x φ

/--
**Global semantic consequence**: Γ semantically entails φ.

`globalSemCsq Γ φ` means: in every model where all formulas in Γ are true
at all states, φ is also true at all states.

**Notation** (informal): Γ ⊨ φ

**Key property**: This is the semantic counterpart to syntactic derivability (Γ ⊢ φ).

**Soundness theorem**: If Γ ⊢ φ (syntactic), then Γ ⊨ φ (semantic)
**Completeness theorem**: If Γ ⊨ φ (semantic), then Γ ⊢ φ (syntactic)

Together these show that syntax and semantics align perfectly!

**Why "global"?** Because we require truth at ALL states in the model, not just
at a specific designated state. This is the standard notion for modal logic.
-/
def globalSemCsq (Γ : Ctx) (φ : Form) : Prop :=
  ∀ (F : Frame.{0}) v, forcesCtx F v Γ → ∀ x, forces F v x φ

------------------------------------------------------------------------------
-- § 4. Basic Simplification Lemmas
------------------------------------------------------------------------------

/-- Bottom is always false - definitional equality. -/
@[simp] lemma forces_bot {F : Frame} {v} {x} :
  forces F v x Form.bot = False := rfl

/-- Conjunction semantics - unfolds by definition. -/
@[simp] lemma forces_and {F : Frame} {v} {x} {φ ψ} :
  forces F v x (φ & ψ) ↔ (forces F v x φ ∧ forces F v x ψ) := Iff.rfl

/-- Implication semantics - unfolds by definition. -/
@[simp] lemma forces_impl {F : Frame} {v} {x} {φ ψ} :
  forces F v x (φ ⊃ ψ) ↔ (forces F v x φ → forces F v x ψ) := Iff.rfl

/-- Box semantics - universal quantification over accessible worlds. -/
@[simp] lemma forces_box {F : Frame} {v} {x} {φ} :
  forces F v x (□ φ) ↔ (∀ y, F.rel x y → forces F v y φ) := Iff.rfl

/--
**Negation semantics**: Object-language negation equals meta-level negation.

`forces F v x (¬φ) ↔ ¬(forces F v x φ)`

**Why this works**: Negation is defined as φ → ⊥, and ⊥ is false.
So ¬φ is true iff φ → False is true iff φ is false.

**Significance**: This shows our encoding of negation via implication correctly
captures the intended semantics.
-/
@[simp] lemma forces_neg {F : Frame} {v} {x} {φ} :
  forces F v x (∼ φ) ↔ ¬ forces F v x φ := by
  simp [neg, forces]

/--
**Negation (alternative Form)**: Sometimes more convenient to have it "backwards".

`¬(forces F v x φ) ↔ forces F v x (¬φ)`
-/
lemma not_forces_iff {F : Frame} {v} {x} {φ} :
  (¬ forces F v x φ) ↔ forces F v x (∼ φ) :=
  forces_neg.symm

/--
**Diamond semantics**: Possibility as existential quantification.

`forces F v x (◇φ) ↔ ∃y. F.rel x y ∧ forces F v y φ`

**Intuition**: ◇φ is true at x iff there exists an accessible world where φ holds.

**Derivation**: Since ◇φ is defined as ¬□¬φ, we have:
- ◇φ is true at x
- iff ¬□¬φ is true at x
- iff ¬(∀y. R(x,y) → ¬φ at y)
- iff ∃y. R(x,y) ∧ φ at y

**Classical reasoning**: This requires classical logic to convert ¬∀ to ∃¬.

**Philosophical meaning**:
- Possibility: "φ is possible" = "φ holds in some accessible world"
- Knowledge: "possibly φ" = "consistent with what is known"
- Time: "eventually φ" = "φ holds at some future time"
-/
@[simp] lemma forces_diamond {F : Frame} {v} {x} {φ} :
  forces F v x (◇ φ) ↔ ∃ y, F.rel x y ∧ forces F v y φ := by
  classical
  simp [dia, neg, forces, _root_.imp_false]

/-- **Simp-friendly version of diamond semantics** for automation. -/
lemma forces_exists {F : Frame} {v} {x} {φ} :
  forces F v x (◇ φ) ↔ ∃ y, F.rel x y ∧ forces F v y φ :=
  forces_diamond

------------------------------------------------------------------------------
-- § 5. Monotonicity and Weakening
------------------------------------------------------------------------------

namespace ForcesCtx

variable {F : Frame} {v : Nat → F.states → Prop}

/--
**Weakening (monotonicity) for contexts**: If Γ ⊆ Δ and all of Δ is true,
then all of Γ is true.

This is a fundamental structural property: having more assumptions can't make
previous assumptions false.

**Logical principle**: Weakening is one of the structural rules of logic.
It says that adding extra hypotheses doesn't invalidate existing ones.
-/
lemma weaken_of_subset {Γ Δ : Ctx} (h : Γ ⊆ Δ) :
  forcesCtx F v Δ → forcesCtx F v Γ := by
  intro hΔ φ x hφΓ
  exact hΔ φ x (h hφΓ)

/--
**Union of contexts**: If both contexts hold, their union holds.

**Intuition**: If both sets of assumptions are satisfied, then their combination
is satisfied.
-/
lemma union {Γ Δ : Ctx}
  (hΓ : forcesCtx F v Γ) (hΔ : forcesCtx F v Δ) :
  forcesCtx F v (Γ ∪ Δ) := by
  intro φ x hmem
  have : (φ ∈ Γ) ∨ (φ ∈ Δ) := by
    simpa [Set.mem_union] using hmem
  cases this with
  | inl hΓmem => exact hΓ φ x hΓmem
  | inr hΔmem => exact hΔ φ x hΔmem

/--
**Insertion of globally true formula**: If φ holds everywhere, adding it to
the context preserves forcing.

**Usage**: Often in completeness proofs, we need to add formulas that are
already true everywhere without breaking the context.
-/
lemma insert_of_global {Γ : Ctx} {φ : Form}
    (hφ : ∀ x, forces F v x φ) (hΓ : forcesCtx F v Γ) :
    forcesCtx F v (Set.insert φ Γ) := by
  intro ψ x hmem
  classical
  have h' : (ψ = φ) ∨ (ψ ∈ Γ) := by
    simpa [Set.insert] using hmem
  cases h' with
  | inl hEq => subst hEq; exact hφ x
  | inr hΓmem => exact hΓ ψ x hΓmem

/--
**Monotonicity of semantic consequence**: Adding assumptions preserves entailments.

If Γ ⊨ φ and Γ ⊆ Δ, then Δ ⊨ φ.

**Logical principle**: This is semantic weakening. It says that valid inferences
remain valid when you add more assumptions.

**Usage**: Crucial for modular reasoning - you can strengthen your assumptions
without invalidating previous conclusions.
-/
lemma globalSemCsq_monotone_left {Γ Δ : Ctx} {φ : Form}
    (hsub : Γ ⊆ Δ) (h : globalSemCsq Γ φ) :
    globalSemCsq Δ φ := by
  intro F v hΔ x
  have hΓ : forcesCtx F v Γ := weaken_of_subset hsub hΔ
  exact h F v hΓ x

end ForcesCtx

------------------------------------------------------------------------------
-- § 6. Valuation Operations
------------------------------------------------------------------------------

/--
**Restriction of valuation to subtype**: When restricting to a subset of states,
restrict the valuation accordingly.

**Usage**: When working with subframes, we need to restrict the valuation to
only the states in the subframe.

**Type**: Converts `Nat → F.states → Prop` to `Nat → {x // x ∈ S} → Prop`
-/
def restrictVal {F : Frame} (v : Nat → F.states → Prop)
    (S : Set F.states) : Nat → {x // x ∈ S} → Prop :=
  fun n x => v n x.1

/--
**Update a single variable**: Modify the valuation for one variable.

**Definition**: `updateVar v n₀ P` is the valuation that:
- Assigns P to variable n₀
- Keeps v's assignment for all other variables

**Usage**: In completeness proofs, we often need to construct specific valuations
that test certain properties. Updating a single variable is a common operation.

**Example**: To test reflexivity, we might set variable 0 to be true exactly
at worlds accessible from a fixed point x.
-/
def updateVar {F : Frame} (v : Nat → F.states → Prop)
    (n0 : Nat) (P : F.states → Prop) : Nat → F.states → Prop :=
  fun n x => if n = n0 then P x else v n x

------------------------------------------------------------------------------
-- § 7. Generated Subframes
------------------------------------------------------------------------------

/--
**Generated set**: The forward closure from A under the accessibility relation.

`Generated F A x` means x is reachable from some state in A by following
finitely many R-steps.

**Inductive definition**:
- base: If x ∈ A, then x is generated
- step: If x is generated and R(x,y), then y is generated

**Intuition**: This is the "shadow" cast by A through the accessibility relation.
It's all the states you can reach starting from A.

**Modal significance**: In modal logic, Generated F {x} is the "generated subframe"
from x - the part of the frame that's "visible" from x using modal operators.

**Connection to reachability**: Generated F A is closely related to reachability,
but allows starting from a SET of states rather than just one.
-/
inductive Generated (F : Frame) (A : Set F.states) : F.states → Prop
  | base {x} (hx : x ∈ A) : Generated F A x
  | step {x y} (hx : Generated F A x) (hxy : F.rel x y) : Generated F A y

------------------------------------------------------------------------------
-- § 8. Successor-Closed Sets and Subframes
------------------------------------------------------------------------------

/--
**Successor-closed set**: A set closed under taking successors.

`isSuccClosed F S` means: if x ∈ S and R(x,y), then y ∈ S.

**Intuition**: You can't "leave" S by following an edge in the frame.

**Why important?** Successor-closed sets support subframes where truth is preserved.
If we restrict attention to a successor-closed set, formulas have the same truth
values as in the original frame.

**Examples**:
- The whole frame is successor-closed
- Generated sets are successor-closed
- The intersection of successor-closed sets is successor-closed
-/
def isSuccClosed (F : Frame) (S : Set F.states) : Prop :=
  ∀ {x y}, x ∈ S → F.rel x y → y ∈ S

/--
**Generated sets are successor-closed**: Closure under the step rule means
successor-closure.

This is immediate from the `step` constructor of Generated.
-/
lemma Generated.succClosed {F : Frame} {A : Set F.states} :
  isSuccClosed F {x | Generated F A x} := by
  intro x y hx hxy
  exact Generated.step hx hxy

/--
**Subframe from successor-closed set**: Restrict frame to states in S.

The subframe has:
- States: {x // x ∈ S} (states from S with proof of membership)
- Relation: restriction of F's relation to S

**Key property**: Because S is successor-closed, if x, y ∈ S and R(x,y) in F,
then we can safely say R(x,y) in the subframe.
-/
def subframe (F : Frame) (S : Set F.states) (_hS : isSuccClosed F S) : Frame where
  states := {x // x ∈ S}
  rel    := fun a b => F.rel a.1 b.1

/--
**Truth preservation for subframes**: Formulas have the same truth value in a
successor-closed subframe as in the original frame.

**Theorem**: For x ∈ S where S is successor-closed:
  forces F v x φ ↔ forces (subframe F S) (restrictVal v S) ⟨x, hx⟩ φ

**Proof strategy**: Induction on φ.
- Atomic cases (⊥, var): Trivial by definition
- Boolean cases (∧, →): Use IH
- Box case (□φ): Key case using successor-closure
  - Forward: Accessible states in subframe are accessible in F
  - Backward: Accessible states in F from x are in S (by successor-closure)

**Significance**: This shows we can "zoom in" on successor-closed parts of frames
without changing truth values. Crucial for generated subframe constructions.

**Application**: In completeness proofs, we often construct canonical models and
then restrict to generated subframes to ensure certain properties hold.
-/
lemma forces_subframe_iff
    {F : Frame} {S : Set F.states} (hS : isSuccClosed F S)
    (v : Nat → F.states → Prop)
    (x : F.states) (hx : x ∈ S) (φ : Form) :
    forces F v x φ
      ↔ forces (subframe F S hS) (restrictVal v S) ⟨x, hx⟩ φ := by
  induction φ generalizing x with
  | bot => simp [forces]
  | var n => simp [forces, restrictVal]
  | and φ ψ ihφ ihψ => simp [forces, ihφ x hx, ihψ x hx]
  | impl φ ψ ihφ ihψ => simp [forces, ihφ x hx, ihψ x hx]
  | box φ ih =>
      -- The key modal case using successor-closure
      constructor
      · -- Forward: □φ in F implies □φ in subframe
        intro h y' hrel
        rcases y' with ⟨y, hyS⟩
        exact (ih y hyS).mp (h y hrel)
      · -- Backward: □φ in subframe implies □φ in F
        intro h y hyF
        -- Key: y must be in S by successor-closure
        have hyS : y ∈ S := hS hx hyF
        exact (ih y hyS).mpr (h ⟨y, hyS⟩ hyF)

/--
**Generated subframe from A**: The subframe consisting of all states
reachable from A.

This combines:
1. Generated F A: the set of reachable states
2. Generated.succClosed: proof this set is successor-closed
3. subframe: the actual subframe construction

**Usage**: The standard way to construct generated subframes in modal logic.
-/
def genSubframe (F : Frame) (A : Set F.states) : Frame :=
  subframe F {x | Generated F A x} Generated.succClosed

/--
**Truth preservation for generated subframes**: Convenience lemma combining
generated set construction with truth preservation.

**Corollary** of forces_subframe_iff specialized to generated subframes.
-/
lemma forces_genSubframe_iff
    {F : Frame} {A : Set F.states} (v : Nat → F.states → Prop)
    (x : F.states) (hx : Generated F A x) (φ : Form) :
    forces F v x φ
      ↔ forces (genSubframe F A) (restrictVal v {x | Generated F A x}) ⟨x, hx⟩ φ := by
  simpa [genSubframe] using forces_subframe_iff Generated.succClosed v x hx φ

------------------------------------------------------------------------------
-- § 9. Product Frames
------------------------------------------------------------------------------

/--
**Product of frames**: Pointwise accessibility on pairs.

The product F × G has:
- States: pairs (x, y) where x ∈ F.states and y ∈ G.states
- Relation: (x₁, y₁) R (x₂, y₂) iff F.rel x₁ x₂ AND G.rel y₁ y₂

**Intuition**: Both components must advance simultaneously.

**Applications**:
- Multi-agent systems: combine multiple agents' accessibility relations
- Temporal logic: product of time and state spaces
- Bisimulation games: product of two models

**Property**: The product construction preserves many frame properties
(reflexivity, transitivity, etc.).
-/
def Frame.prod (F G : Frame) : Frame where
  states := F.states × G.states
  rel := fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ => F.rel x₁ x₂ ∧ G.rel y₁ y₂

/--
**Product valuation**: Conjunctive combination of component valuations.

For a variable n at state (x, y):
  prodVal vF vG n (x, y) := vF n x ∧ vG n y

**Why conjunctive?** This is the natural choice making formulas behave
componentwise on products.

**Alternative**: Could use disjunction, but conjunction is standard and more useful.
-/
def prodVal {F G : Frame}
    (vF : Nat → F.states → Prop) (vG : Nat → G.states → Prop) :
    Nat → (F.states × G.states) → Prop :=
  fun n ⟨x, y⟩ => vF n x ∧ vG n y

end Modal
