/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen
Converted to Lean 4 with improvements
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic

namespace ModalPath

/-! # Reachability in Relations

This file develops the theory of reachability for binary relations, which is fundamental
for modal logic, graph theory, and program verification.

## Mathematical Background

**Reachability**: Given a binary relation R on a set α, we say y is **reachable** from x
if there exists a finite sequence of R-steps from x to y:
  x →R x₁ →R x₂ →R ... →R xₙ = y

This is also called the **reflexive-transitive closure** of R, denoted R*.

**Key properties**:
- Reflexive: every element reaches itself (via the empty path)
- Transitive: if x reaches y and y reaches z, then x reaches z
- Contains R: every single R-step is a reachability path
- Minimal: it's the smallest relation with these three properties

## Design Choices

**Why lists?** We represent paths explicitly as lists of intermediate states. This makes
proofs constructive and allows us to reason about the "witness" of reachability.

**Alternative**: We could define reachability inductively (see ReachableInd below). Both
approaches are equivalent, but the list-based definition is often easier to work with.

## Applications

**Modal logic**: In Kripke frames, reachability determines which worlds can be accessed
through iterated modal operators. This is crucial for:
- Generated subframes (worlds reachable from a point)
- Path semantics (formulas true along paths)
- Invariance proofs

**Graph theory**: Reachability is graph connectivity
**Program verification**: Reachability in state transition systems
**Type theory**: Subtyping and type conversion chains

## Main Results

- Reachability is reflexive and transitive (making it a preorder)
- Single steps imply reachability (containsR)
- Reachability is the unique smallest reflexive-transitive relation containing R
- Equivalence with inductive definition (for convenience in proofs)
-/

variable {α : Type*}

------------------------------------------------------------------------------
-- § 1. Path Definitions
------------------------------------------------------------------------------

/--
**Path through a list**: A sequence of R-steps following the list.

`Path R x [y₁, y₂, ..., yₙ]` means:
  R x y₁ ∧ R y₁ y₂ ∧ ... ∧ R yₙ₋₁ yₙ

**Empty path**: `Path R x []` is always true (no steps required).

**Intuition**: The list records the intermediate states visited along the path.
This is like a "proof term" for reachability - it witnesses how y is reachable from x.

**Example**: In a graph, `Path Edge start [a, b, c]` means:
  start →Edge a →Edge b →Edge c
-/
def Path (R : α → α → Prop) : α → List α → Prop
  | _, [] => True                    -- Empty path: no steps needed
  | x, y :: ys => R x y ∧ Path R y ys  -- Step from x to y, then continue from y

/--
**Last element of a path**: Where we end up after following the path.

`pathLast R x [y₁, y₂, ..., yₙ]` returns yₙ (or x if the list is empty).

**Invariant**: If `Path R x l`, then we can reach `pathLast R x l` from x by following l.

**Implementation note**: This is a simple recursive function that walks to the end of the list.
For empty list, we stay at x. For non-empty list, we recursively find the last element.
-/
def pathLast (R : α → α → Prop) : α → List α → α
  | x, [] => x                      -- Empty path ends at x
  | _, y :: ys => pathLast R y ys   -- Continue from y through the rest

/--
**Reachability**: The reflexive-transitive closure of R.

`Reachable R x y` means: there exists a finite sequence of R-steps from x to y.

**Definition**: We witness reachability by a list l such that:
1. `Path R x l` - we can follow R through l starting from x
2. `pathLast R x l = y` - following l from x leads to y

**Examples**:
- `Reachable R x x` via the empty path []
- If `R x y`, then `Reachable R x y` via the path [y]
- If `R x y` and `R y z`, then `Reachable R x z` via the path [y, z]

**Key property**: This is the smallest relation that:
- Contains R (single steps)
- Is reflexive (x reaches x)
- Is transitive (x→y→z implies x→z)

**Connection to modal logic**: In Kripke frames, `Reachable rel x y` means
y is in the generated subframe from x. This determines which worlds are
"modally accessible" through repeated application of □.
-/
def Reachable (R : α → α → Prop) (x y : α) : Prop :=
  ∃ l : List α, Path R x l ∧ pathLast R x l = y

------------------------------------------------------------------------------
-- § 2. Basic Properties of Paths
------------------------------------------------------------------------------

/-- Empty path is always valid - no steps to verify. -/
@[simp]
lemma path_nil {R : α → α → Prop} {x : α} : Path R x [] := trivial

/-- Path through y::ys means: step from x to y, then path from y through ys. -/
@[simp]
lemma path_cons {R : α → α → Prop} {x y : α} {ys : List α} :
    Path R x (y :: ys) ↔ R x y ∧ Path R y ys := Iff.rfl

/-- Empty path ends where it started. -/
@[simp]
lemma pathLast_nil {R : α → α → Prop} {x : α} : pathLast R x [] = x := rfl

/-- Last element of y::ys is the last element of ys starting from y. -/
@[simp]
lemma pathLast_cons {R : α → α → Prop} {x y : α} {ys : List α} :
    pathLast R x (y :: ys) = pathLast R y ys := rfl

------------------------------------------------------------------------------
-- § 3. Core Properties of Reachability
------------------------------------------------------------------------------

/--
**Reflexivity of reachability**: Every element reaches itself.

**Proof**: The empty path [] witnesses that x reaches x.
- `Path R x []` is true by definition
- `pathLast R x [] = x` by definition

**Significance**: This is why reachability is the REFLEXIVE-transitive closure.
Even if R is not reflexive, Reachable R is reflexive.

**Modal logic application**: In any Kripke frame, every world is in its own
generated subframe.
-/
theorem Reachable.refl {R : α → α → Prop} (x : α) : Reachable R x x := by
  use []
  simp [Path, pathLast]

/--
**Right extension**: If x reaches y and there's one more R-step from y to z,
then x reaches z.

**Proof strategy**: Extend the path witnessing x →* y by appending z.
- Given: path l from x to y, and R y z
- Want: path from x to z
- Construction: append z to the path

**Induction on the path l**:
- Base (l = []): Then y = x, so R x z. Use path [z]
- Step (l = hd::tl): We have R x hd and a path from hd to y
  - By IH, extend the path from hd to z
  - Prepend the step R x hd

**Significance**: This is a key lemma for building up reachability proofs.
It's used extensively in proving transitivity and in modal logic proofs.
-/
lemma reachRight {R : α → α → Prop} {x y z : α} :
    Reachable R x y → R y z → Reachable R x z := by
  intro ⟨l, hPath, hLast⟩ hRyz
  induction l generalizing x with
  | nil =>
      -- Base case: l = [], so y = x
      use [z]
      constructor
      · simp [Path]
        -- Need: R x z
        -- We have: y = x and R y z
        subst hLast
        exact hRyz
      · simp [pathLast]
  | cons hd tl ih =>
      -- Step case: l = hd::tl
      -- We have: R x hd and Path R hd tl with pathLast R hd tl = y
      simp [Path] at hPath
      obtain ⟨hRxhd, hPathtl⟩ := hPath
      simp [pathLast] at hLast
      -- By IH, extend the path from hd to z
      obtain ⟨l', hPath', hLast'⟩ := ih hPathtl hLast
      -- Construct path hd::l' from x to z
      use hd :: l'
      constructor
      · simp [Path]
        exact ⟨hRxhd, hPath'⟩
      · simp [pathLast]
        exact hLast'

/--
**Transitivity of reachability**: If x reaches y and y reaches z, then x reaches z.

**Proof strategy**: Concatenate the two paths.
- Given: path l₁ from x to y, and path l₂ from y to z
- Want: path from x to z
- Construction: follow l₁ to reach y, then follow l₂ to reach z

**Induction on l₁**:
- Base (l₁ = []): Then x = y, so just use l₂
- Step (l₁ = hd::tl): We have R x hd and a path from hd to y
  - By IH, we get a path from hd to z
  - Prepend the step R x hd

**Significance**: This proves that reachability is a preorder (reflexive + transitive).
Combined with reflexivity, this is why it's called the reflexive-TRANSITIVE closure.

**Alternative view**: Reachability is like addition on natural numbers:
- Reflexivity is like n + 0 = n
- Transitivity is like (a + b) + c = a + (b + c)
-/
theorem Reachable.trans {R : α → α → Prop} {x y z : α} :
    Reachable R x y → Reachable R y z → Reachable R x z := by
  intro ⟨l1, hPath1, hLast1⟩ ⟨l2, hPath2, hLast2⟩
  induction l1 generalizing x y z with
  | nil =>
      -- Base case: l1 = [], so x = y
      simp [pathLast] at hLast1
      subst hLast1
      -- Just use l2 as the path from x (= y) to z
      use l2
  | cons hd tl ih =>
      -- Step case: l1 = hd::tl
      -- We have: R x hd and a path from hd to y
      simp [Path] at hPath1
      obtain ⟨hRxhd, hPathtl⟩ := hPath1
      simp [pathLast] at hLast1
      -- By IH, combine the path from hd to y with the path from y to z
      obtain ⟨l', hPath', hLast'⟩ := ih hPathtl hLast1 hPath2 hLast2
      -- Construct path hd::l' from x to z
      use hd :: l'
      constructor
      · simp [Path]
        exact ⟨hRxhd, hPath'⟩
      · simp [pathLast]
        exact hLast'

/--
**Single steps imply reachability**: If R x y, then Reachable R x y.

**Proof**: Use the singleton path [y].
- `Path R x [y]` means R x y ∧ Path R y [] = R x y ∧ True
- `pathLast R x [y] = y`

**Significance**: This shows that R ⊆ Reachable R.
Reachability is an extension of R, not a replacement.

**Terminology**: R is the "base relation" and Reachable R is its reflexive-transitive closure.
-/
lemma containsR {R : α → α → Prop} {x y : α} : R x y → Reachable R x y := by
  intro hRxy
  use [y]
  simp [Path, pathLast, hRxy]

------------------------------------------------------------------------------
-- § 4. Minimality: Reachability as the Smallest Reflexive-Transitive Closure
------------------------------------------------------------------------------

/--
**Minimality theorem**: Reachability is the smallest reflexive-transitive relation
containing R.

**Theorem**: Let S be any relation that is:
1. Reflexive: ∀x. S x x
2. Transitive: ∀x y z. S x y → S y z → S x z
3. Contains R: ∀x y. R x y → S x y

Then: Reachable R ⊆ S

In other words: ∀x y. Reachable R x y → S x y

**Proof strategy**: Induction on the path witnessing reachability.
- Base (empty path): By reflexivity of S
- Step (path hd::tl): Combine R x hd (hence S x hd) with IH using transitivity

**Significance**: This characterizes reachability uniquely:
- Existence: Reachable R satisfies all three properties
- Uniqueness: Any other relation satisfying them contains Reachable R

Therefore, Reachable R is the UNIQUE smallest reflexive-transitive relation containing R.

**Categorical perspective**: Reachability is the "free" reflexive-transitive relation
generated by R. It's the universal construction in the category of preorders.

**Applications**:
- Proves that different definitions of reachability coincide
- Shows reachability is well-defined and canonical
- Used to transfer properties between different closure constructions
-/
theorem smallest {R S : α → α → Prop}
    (reflS : Reflexive S) (transS : Transitive S)
    (hContains : ∀ x y, R x y → S x y) :
    ∀ x y, Reachable R x y → S x y := by
  intro x z ⟨l, hPath, hLast⟩
  induction l generalizing x with
  | nil =>
      -- Base case: empty path, so z = x
      simp [pathLast] at hLast
      subst hLast
      -- Use reflexivity of S
      exact reflS x
  | cons hd tl ih =>
      -- Step case: path hd::tl from x to z
      -- We have: R x hd and a path from hd to z
      simp [Path] at hPath
      obtain ⟨hRxhd, hPathtl⟩ := hPath
      simp [pathLast] at hLast
      -- By IH: S hd z
      have hS_hd_z := ih hd hPathtl hLast
      -- By containment: S x hd (from R x hd)
      -- By transitivity: S x z
      exact transS (hContains x hd hRxhd) hS_hd_z

------------------------------------------------------------------------------
-- § 5. Alternative Inductive Characterization
------------------------------------------------------------------------------

/--
**Inductive definition of reachability**: An alternative, more direct definition.

This is closer to how reachability is often defined in textbooks:
- Base case: x reaches x (reflexivity)
- Inductive case: If R x y and y reaches z, then x reaches z

**Comparison with list-based definition**:
- List-based: Explicit witness (constructive)
- Inductive: More abstract, sometimes easier for proofs
- Both are equivalent (proven below)

**When to use which**:
- List-based: When you need the actual path (e.g., to extract information)
- Inductive: When you only care about existence (e.g., in logical arguments)
-/
inductive ReachableInd (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : ReachableInd R x x
  | step {x y z : α} : R x y → ReachableInd R y z → ReachableInd R x z

/--
**Equivalence of definitions**: The list-based and inductive definitions coincide.

**Theorem**: Reachable R x y ↔ ReachableInd R x y

This proves that both definitions capture the same mathematical concept.
Having both available gives us flexibility in proofs.

**Proof sketch**:

**(→) List-based implies inductive**:
Induction on the list l witnessing reachability.
- Base (l = []): Use ReachableInd.refl
- Step (l = hd::tl): Use ReachableInd.step with R x hd and IH

**(←) Inductive implies list-based**:
Induction on the derivation of ReachableInd R x y.
- refl case: Use the empty list []
- step case: Combine the single step with the IH using transitivity

**Significance**:
- Validates our choice of definition (it matches the standard one)
- Allows us to switch between representations as convenient
- Shows the list-based definition is not "over-specified"

**Philosophical note**: The equivalence of these definitions is not trivial!
It's a theorem that needs proof. This is similar to how different axiomatizations
of the natural numbers (Peano axioms vs. set-theoretic definition) need to be
proven equivalent.
-/
theorem reachable_iff_reachableInd {R : α → α → Prop} {x y : α} :
    Reachable R x y ↔ ReachableInd R x y := by
  constructor
  · -- (→) List-based implies inductive
    intro ⟨l, hPath, hLast⟩
    induction l generalizing x y with
    | nil =>
        -- Empty path: use reflexivity
        simp [pathLast] at hLast
        subst hLast
        exact ReachableInd.refl x
    | cons hd tl ih =>
        -- Path hd::tl: use step constructor
        simp [Path] at hPath
        obtain ⟨hRxhd, hPathtl⟩ := hPath
        simp [pathLast] at hLast
        -- By IH: ReachableInd R hd y
        have h_hd_y := ih hPathtl hLast
        -- Apply step constructor: R x hd and ReachableInd R hd y gives ReachableInd R x y
        exact ReachableInd.step hRxhd h_hd_y
  · -- (←) Inductive implies list-based
    intro h
    induction h with
    | refl x =>
        -- Reflexivity: use empty path
        exact Reachable.refl x
    | step hRxy _ ihReach =>
        -- Step: R x y and (by IH) Reachable R y z
        -- Need: Reachable R x z
        -- Combine using transitivity
        exact Reachable.trans (containsR hRxy) ihReach

end ModalPath
