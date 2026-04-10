/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Author: Huub Vromen
-/

import ModalLogic.Semantics.Semantics
import ModalLogic.Semantics.Paths

namespace BasicModal
open Modal
open ModalPath
set_option autoImplicit false

/-! # Frame Definability

This file establishes one of the most beautiful results in modal logic: the correspondence
between modal axioms and frame properties. This is known as **correspondence theory**.

## The Central Question

When does a modal formula φ characterize a geometric property of frames?

**Answer**: Many important modal axioms correspond exactly to first-order properties
of the accessibility relation. This file proves several fundamental correspondences.

## Mathematical Background

**Definability**: A formula φ defines a frame class F if:
  - f ∈ F ⟺ φ is valid in f

This means φ is a "modal test" for membership in F - you can check if a frame is in F
by testing whether φ holds everywhere in that frame.

**Why this matters**:
1. Provides semantic meaning to syntactic axioms
2. Allows us to reason about frame properties modally
3. Shows the expressive power (and limitations) of modal logic
4. Connects proof theory (axioms) to model theory (frame properties)

## Main Correspondences Proven

| Modal Axiom | Frame Property | Name |
|-------------|----------------|------|
| □p → p | Reflexive | T axiom |
| p → □◇p | Symmetric | B axiom |
| □p → □□p | Transitive | 4 axiom |
| ◇p → □◇p | Euclidean | 5 axiom |
| □p → ◇p | Serial | D axiom |

## Proof Strategy

For each correspondence φ ↔ P:
1. **Forward (⇒)**: If f has property P, show φ is valid in f
   - Usually straightforward semantic argument
2. **Backward (⇐)**: If φ is valid in f, show f has property P
   - Construct a clever valuation that "tests" for the property
   - Show that validity of φ forces the property to hold

The backward direction is the interesting part - we use the expressive power of
modal logic to "force" frame properties to hold.

## References

- Van Benthem, "Modal Correspondence Theory" (1984)
- Blackburn, de Rijke, Venema, "Modal Logic" (2001), Chapter 3
- Sahlqvist correspondence theorem (generalization)
-/

------------------------------------------------------------------------------
-- § 1. Core Definition: Frame Definability
------------------------------------------------------------------------------

/--
**Frame Definability**: A formula φ defines a frame class F if membership in F
is characterized by validity of φ.

**Definition**: Defines φ F means: ∀f. (f ∈ F ↔ fValid φ f)

**Intuition**: The formula φ is a "modal test" for the frame property.
- If φ is valid in f, then f must have the property (f ∈ F)
- If f has the property, then φ must be valid in f

**Examples**:
- □p → p defines reflexive frames
- □p → □□p defines transitive frames
- Not every frame class is definable! (see undefinability results)

**Important distinction**:
- fValid φ f: φ is true at all points in all models on frame f
- This is stronger than just "φ is true at some point" or "in some model"
-/
def Defines (φ : Form) (F : Set Modal.Frame.{0}) : Prop :=
  ∀ (f : Modal.Frame.{0}), (f ∈ F) ↔ (Modal.fValid φ f)

------------------------------------------------------------------------------
-- § 2. Frame Properties and Classes
------------------------------------------------------------------------------

section FrameProperties

variable {α : Type*}

/--
**Euclidean property**: If x relates to both y and z, then y relates to z.

Formally: ∀x y z. R(x,y) ∧ R(x,z) → R(y,z)

**Intuition**: If two worlds are both accessible from a common world,
they can access each other. This creates clusters of mutually accessible worlds.

**Alternative characterization**: Combined with reflexivity, this gives an
equivalence relation (see equivRefEuclid below).

**Modal correspondence**: Euclidean property ↔ axiom ◇φ → □◇φ (the "5 axiom")

**Applications**:
- S5 modal logic (knowledge logic with perfect information)
- Epistemic logic where agents have common knowledge
-/
def Euclidean (R : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, R x y → R x z → R y z

/--
**Serial property**: Every world has at least one successor.

Formally: ∀x. ∃y. R(x,y)

**Intuition**: No "dead ends" - from every world, there is at least one
accessible world.

**Modal correspondence**: Serial property ↔ axiom □p → ◇p (the "D axiom")

**Applications**:
- Deontic logic: there is always an ideal world (seriality ensures obligations
  are consistent — what is obligatory is at least possible)
- KD45 logic: deontic logic with introspection
-/
def Serial (R : α → α → Prop) : Prop :=
  ∀ x, ∃ y, R x y

end FrameProperties

/--
**Reflexive frames**: Every world can access itself.

Formally: ∀x. R(x,x)

**Modal correspondence**: □p → p (the "T axiom")

**Intuition**: What is necessarily true must be actually true.
If something holds at all accessible worlds, it holds at the current world
(since the current world is accessible from itself).

**Applications**: Most epistemic and deontic logics assume reflexivity
-/
abbrev refClass : Set Modal.Frame.{0} := {f : Modal.Frame.{0} | Reflexive f.rel}

/--
**Symmetric frames**: Accessibility is bidirectional.

Formally: ∀x y. R(x,y) → R(y,x)

**Modal correspondence**: p → □◇p (the "B axiom")

**Intuition**: If y is accessible from x, then x is accessible from y.
Information flows both ways.

**Applications**: Less common than other properties, but appears in some
epistemic logics and in the study of equivalence relations.
-/
abbrev symmClass : Set Modal.Frame.{0} := {f : Modal.Frame.{0} | Symmetric f.rel}

/--
**Transitive frames**: Accessibility is transitive.

Formally: ∀x y z. R(x,y) ∧ R(y,z) → R(x,z)

**Modal correspondence**: □p → □□p (the "4 axiom")

**Intuition**: If y is accessible from x and z from y, then z is accessible from x.
You can "chain" accessibility relations.

**Philosophical meaning**: "If you know that you know φ, then you know φ"
This is the key axiom distinguishing S4 from T.

**Applications**: S4 modal logic, provability logic, topological semantics
-/
abbrev transClass : Set Modal.Frame.{0} := {f : Modal.Frame.{0} | Transitive f.rel}

/--
**Euclidean frames**: Satisfy the Euclidean property.

Formally: ∀x y z. R(x,y) ∧ R(x,z) → R(y,z)

**Modal correspondence**: ◇p → □◇p (the "5 axiom")

**Key property**: Reflexive + Euclidean = Equivalence relation (proven below)
-/
abbrev euclidClass : Set Modal.Frame.{0} := {f : Modal.Frame.{0} | Euclidean f.rel}

/--
**Serial frames**: Every world has at least one successor.

Formally: ∀x. ∃y. R(x,y)

**Modal correspondence**: □p → ◇p (the "D axiom")

**Key property**: Reflexivity implies seriality (every world accesses itself).
-/
abbrev serialClass : Set Modal.Frame.{0} := {f : Modal.Frame.{0} | Serial f.rel}

/--
**Equivalence frames**: Accessibility is an equivalence relation.

An equivalence relation is reflexive, symmetric, and transitive.

**Modal correspondence**: Axioms T + 5, or equivalently T + B + 4

**Intuition**: Worlds are partitioned into equivalence classes.
Within each class, every world can access every other world (including itself).

**Applications**:
- S5 modal logic (the strongest standard modal logic)
- Epistemic logic with common knowledge
- Reasoning about indistinguishability
-/
abbrev equivClass : Set Modal.Frame.{0} := {f : Modal.Frame.{0} | Equivalence f.rel}

/--
**Reflexive-symmetric frames**: Frames that are both reflexive and symmetric.

This is the frame class for KTB (Brouwerian) modal logic.
-/
abbrev refSymmClass : Set Modal.Frame.{0} := refClass ∩ symmClass

/--
**Symmetric-transitive frames**: Frames that are both symmetric and transitive.

This is the frame class for KB4 modal logic.
-/
abbrev symmTransClass : Set Modal.Frame.{0} := symmClass ∩ transClass

/--
**Reflexive-transitive frames**: Frames that are both reflexive and transitive.

This is the frame class for S4 modal logic.

**Properties**: These are preorder relations (reflexive partial orders without antisymmetry)

**Applications**: S4 modal logic, topological reasoning, knowledge representation
-/
abbrev refTransClass : Set Modal.Frame.{0} := refClass ∩ transClass

/--
**Serial-symmetric frames**: Frames that are both serial and symmetric.

This is the frame class for KDB modal logic.
-/
abbrev serialSymmClass : Set Modal.Frame.{0} := serialClass ∩ symmClass

/--
**Serial-transitive frames**: Frames that are both serial and transitive.

This is the frame class for KD4 modal logic.
-/
abbrev serialTransClass : Set Modal.Frame.{0} := serialClass ∩ transClass

/--
**Transitive-Euclidean frames**: Frames that are both transitive and Euclidean.

This is the frame class for K45 modal logic.
-/
abbrev transEuclidClass : Set Modal.Frame.{0} := transClass ∩ euclidClass

/--
**Symmetric-Euclidean frames**: Frames that are both symmetric and Euclidean.

This is the frame class for KB5 modal logic. Since symmetric + Euclidean
implies transitive, these frames are also transitive.
-/
abbrev symmEuclidClass : Set Modal.Frame.{0} := symmClass ∩ euclidClass

------------------------------------------------------------------------------
-- § 3. Relationships Between Frame Classes
------------------------------------------------------------------------------

/--
**Reflexivity implies seriality**: Every reflexive frame is serial.

If R(x,x) for all x, then certainly ∃y. R(x,y) (take y = x).
-/
theorem refClass_subset_serialClass : refClass ⊆ serialClass := by
  intro f hRefl x
  exact ⟨x, hRefl x⟩

/--
**Equivalence via reflexivity and Euclidean property**:
A frame has an equivalence relation iff it is reflexive and Euclidean.

**Theorem**: Equivalence ↔ Reflexive ∧ Euclidean

This is a beautiful result: the Euclidean property encodes both symmetry and
transitivity when combined with reflexivity!

**Proof sketch**:
- (⇒) Equivalence implies reflexive (trivial) and Euclidean (symmetry + transitivity)
- (⇐) Reflexive + Euclidean implies symmetric:
      R(x,y) and R(x,x) give R(y,x) by Euclidean
- (⇐) Reflexive + Euclidean implies transitive:
      R(x,y) and R(y,z): first derive R(y,x) by symmetry, then Euclidean on
      R(y,x) and R(y,z) gives R(x,z)

**Significance**: This explains why S5 can be axiomatized by T + 5 instead of T + B + 4.
The 5 axiom alone (with reflexivity) gives us both symmetry and transitivity!
-/
theorem equivRefEuclid (f : Modal.Frame.{0}) :
    (f ∈ equivClass) ↔ (f ∈ (refClass ∩ euclidClass)) := by
  simp only [equivClass, refClass, euclidClass, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · -- (⇒) Equivalence implies reflexive and Euclidean
    intro ⟨hRefl, hSymm, hTrans⟩
    exact ⟨hRefl, fun _ _ _ hxy hxz => hTrans (hSymm hxy) hxz⟩
  · -- (⇐) Reflexive and Euclidean implies equivalence
    intro ⟨hRefl, hEuclid⟩
    refine ⟨hRefl, ?_, ?_⟩
    · -- Symmetric: R(x,y) and R(x,x) give R(y,x) by Euclidean
      intro x y hxy
      exact hEuclid hxy (hRefl x)
    · -- Transitive: R(x,y) → R(y,x) by symmetry above; then
      -- Euclidean on R(y,x) and R(y,z) gives R(x,z)
      intro x y z hxy hyz
      exact hEuclid (hEuclid hxy (hRefl x)) hyz

------------------------------------------------------------------------------
-- § 4. Helper Lemmas: Forward Directions
------------------------------------------------------------------------------

/--
**T axiom is valid in reflexive frames** (forward direction of correspondence).

**Lemma**: If f is reflexive, then □φ → φ is valid in f.

**Proof**: Suppose □φ holds at x. By reflexivity, R(x,x), so φ holds at x.
-/
lemma refHelper : ∀ φ f, f ∈ refClass → Modal.fValid (□ φ ⊃ φ) f := by
  intros _ _ hRefl _ x hBox
  exact hBox x (hRefl x)

/--
**B axiom is valid in symmetric frames** (forward direction).

**Lemma**: If f is symmetric, then φ → □◇φ is valid in f.

**Proof**: Suppose φ holds at x. For any y with R(x,y), by symmetry R(y,x),
so x witnesses ◇φ at y. Therefore □◇φ holds at x.
-/
lemma symmHelper : ∀ φ f, f ∈ symmClass → Modal.fValid (φ ⊃ (□ (◇ φ))) f := by
  intros φ f hSymm v x hφ y hxy hNot
  exact hNot x (hSymm hxy) hφ

/--
**4 axiom is valid in transitive frames** (forward direction).

**Lemma**: If f is transitive, then □φ → □□φ is valid in f.

**Proof**: Suppose □φ at x. For any y with R(x,y) and z with R(y,z),
transitivity gives R(x,z), so φ holds at z.
-/
lemma transHelper : ∀ φ f, f ∈ transClass → Modal.fValid (□ φ ⊃ □ (□ φ)) f := by
  intros _ _ hTrans _ x hBox y hxy z hyz
  exact hBox z (hTrans hxy hyz)

/--
**5 axiom is valid in Euclidean frames** (forward direction).

**Lemma**: If f is Euclidean, then ◇φ → □◇φ is valid in f.

**Proof**: Suppose ◇φ at x, witnessed by some z with R(x,z) and φ at z.
For any y with R(x,y), the Euclidean property on R(x,y) and R(x,z) gives R(y,z),
so z witnesses ◇φ at y. Therefore □◇φ holds at x.
-/
lemma euclidHelper : ∀ φ f, f ∈ euclidClass → Modal.fValid (◇ φ ⊃ □ (◇ φ)) f := by
  intros φ f hEuclid v x hDia y hxy hBoxNeg
  simp [Modal.forces, dia, neg] at hDia
  obtain ⟨z, hxz, hφz⟩ := hDia
  exact hBoxNeg z (hEuclid hxy hxz) hφz

/--
**D axiom is valid in serial frames** (forward direction).

**Lemma**: If f is serial, then □φ → ◇φ is valid in f.

**Proof**: Suppose □φ at x. By seriality, there exists y with R(x,y).
Then φ holds at y (from □φ), so y witnesses ◇φ at x.
-/
lemma serialHelper : ∀ φ f, f ∈ serialClass → Modal.fValid (□ φ ⊃ ◇ φ) f := by
  intros φ f hSerial v x hBox hBoxNeg
  simp [Modal.forces, neg] at hBoxNeg
  obtain ⟨y, hxy⟩ := hSerial x
  exact hBoxNeg y hxy (hBox y hxy)

------------------------------------------------------------------------------
-- § 5. Main Definability Theorems
------------------------------------------------------------------------------

/--
**T axiom defines reflexivity**: The formula □p → p defines exactly the
class of reflexive frames.

**Theorem**: f is reflexive ↔ (□p → p) is valid in f

**Backward direction**: Suppose □p → p is valid in f. Fix x. Define
  v(n,y) := (n = 0) ∧ R(x,y)
Then □p holds trivially at x (since v(0,y) ← R(x,y)), so by validity
p holds at x, giving v(0,x), i.e., R(x,x).
-/
theorem refDef : Defines (□ (Form.var 0) ⊃ (Form.var 0)) refClass := by
  intro f
  constructor
  · exact refHelper (Form.var 0) f
  · intro h x
    let v := fun n y => n = 0 ∧ f.rel x y
    specialize h v x
    simp [Modal.forces, v] at h
    exact h

/--
**B axiom defines symmetry**: The formula p → □◇p defines exactly the
class of symmetric frames.

**Theorem**: f is symmetric ↔ (p → □◇p) is valid in f

**Backward direction**: Suppose p → □◇p is valid. For contradiction, assume
∃x,y. R(x,y) ∧ ¬R(y,x). Define v(n,z) := (n = 0) ∧ ¬R(y,z).
Then p holds at x (since ¬R(y,x)), so □◇p holds at x.
In particular, ◇p holds at y. But ◇p at y requires ∃z. R(y,z) ∧ ¬R(y,z),
which is absurd.
-/
theorem symmDef : Defines ((Form.var 0) ⊃ (□ (◇ (Form.var 0)))) symmClass := by
  intro f
  constructor
  · exact symmHelper (Form.var 0) f
  · intro h
    by_contra hNotSymm
    simp [symmClass, Symmetric] at hNotSymm
    obtain ⟨x, y, hxy, hNotyx⟩ := hNotSymm
    let v := fun n z => n = 0 ∧ ¬f.rel y z
    have hAtX := h v x
    simp [Modal.forces, v, dia, neg] at hAtX
    obtain ⟨w, hyw, hNotyw⟩ := hAtX hNotyx y hxy
    exact hNotyw hyw

/--
**4 axiom defines transitivity**: The formula □p → □□p defines exactly the
class of transitive frames.

**Theorem**: f is transitive ↔ (□p → □□p) is valid in f

**Backward direction**: Suppose □p → □□p is valid. For contradiction, assume
∃x,y,z. R(x,y) ∧ R(y,z) ∧ ¬R(x,z). Define v(n,w) := (n = 0) ∧ R(x,w).
Then □p holds trivially at x, so □□p holds at x.
Instantiating at y gives □p at y, then at z gives R(x,z). Contradiction.
-/
theorem transDef : Defines (□ (Form.var 0) ⊃ □ (□ (Form.var 0))) transClass := by
  intro f
  constructor
  · exact transHelper (Form.var 0) f
  · intro h
    by_contra hNotTrans
    simp only [transClass, Set.mem_setOf_eq] at hNotTrans
    unfold Transitive at hNotTrans
    push_neg at hNotTrans
    obtain ⟨x, y, z, hxy, hyz, hNotxz⟩ := hNotTrans
    let v := fun n w => n = 0 ∧ f.rel x w
    have hBox : Modal.forces f v x (□ (Form.var 0)) := fun w hw => ⟨rfl, hw⟩
    have hBoxBox := h v x hBox
    have hAtZ := hBoxBox y hxy z hyz
    simp only [Modal.forces, v] at hAtZ
    exact hNotxz hAtZ.2

/--
**5 axiom defines Euclidean property**: The formula ◇p → □◇p defines exactly the
class of Euclidean frames.

**Theorem**: f is Euclidean ↔ (◇p → □◇p) is valid in f

**Forward direction**: Proven by euclidHelper above.

**Backward direction**: Suppose ◇p → □◇p is valid. For contradiction, assume
∃x,y,z. R(x,y) ∧ R(x,z) ∧ ¬R(y,z). Define v(n,w) := (n = 0) ∧ w = z.
Then ◇p holds at x (witnessed by z with R(x,z) and v(0,z)).
By validity, □◇p holds at x. In particular ◇p holds at y.
But ◇p at y requires ∃w. R(y,w) ∧ w = z, i.e., R(y,z). Contradiction.
-/
theorem euclidDef : Defines (◇ (Form.var 0) ⊃ □ (◇ (Form.var 0))) euclidClass := by
  intro f
  constructor
  · exact euclidHelper (Form.var 0) f
  · intro h
    by_contra hNotEuclid
    simp only [euclidClass, Set.mem_setOf_eq] at hNotEuclid
    unfold Euclidean at hNotEuclid
    push_neg at hNotEuclid
    obtain ⟨x, y, z, hxy, hxz, hNotyz⟩ := hNotEuclid
    let v := fun n (w : f.states) => n = 0 ∧ w = z
    -- ◇p holds at x: witnessed by z
    have hDia : Modal.forces f v x (◇ (Form.var 0)) := by
      simp [Modal.forces, dia, neg, v]
      exact hxz
    -- By validity, □◇p holds at x
    have hBoxDia := h v x hDia
    -- In particular, ◇p holds at y
    have hDiaY := hBoxDia y hxy
    -- ◇p at y means ∃w. R(y,w) ∧ w = z, i.e., R(y,z)
    simp [Modal.forces, dia, neg, v] at hDiaY
    exact hNotyz hDiaY

/--
**D axiom defines seriality**: The formula □p → ◇p defines exactly the
class of serial frames.

**Theorem**: f is serial ↔ (□p → ◇p) is valid in f

**Forward direction**: Proven by serialHelper above.

**Backward direction**: Suppose □p → ◇p is valid. Fix x. Define
v(n,y) := True. Then □p holds at x (p is true everywhere).
By validity, ◇p holds at x, i.e., ∃y. R(x,y) ∧ True, giving ∃y. R(x,y).
So seriality holds at x.
-/
theorem serialDef : Defines (□ (Form.var 0) ⊃ ◇ (Form.var 0)) serialClass := by
  intro f
  constructor
  · exact serialHelper (Form.var 0) f
  · intro h x
    let v := fun (_n : Nat) (_y : f.states) => True
    have hBox : Modal.forces f v x (□ (Form.var 0)) := fun _ _ => trivial
    have hDia := h v x hBox
    simp [Modal.forces, dia, neg, v] at hDia
    exact hDia

end BasicModal
