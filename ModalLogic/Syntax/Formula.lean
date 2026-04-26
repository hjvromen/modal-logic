/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Formula Type for Modal Logic

This file defines the core formula type for basic modal propositional logic,
representing the formal language in which modal statements are expressed.

## Design Philosophy

**Minimalist core + derived operators**: We define only the essential constructors
(⊥, var, ∧, →, □) and derive everything else (¬, ⊤, ∨, ↔, ◇).

**Why these primitives?**
1. **Mathematical elegance**: Minimal set of independent operators
2. **Proof simplicity**: Induction only needs 5 cases, not 10
3. **Traditional**: Matches standard presentations in modal logic
4. **Functionally complete**: Can express all boolean combinations + modality
-/

import Mathlib.Tactic

namespace BasicModal

------------------------------------------------------------------------------
-- § 1. The Formula Type
------------------------------------------------------------------------------

/--
**Formulas of basic modal propositional logic**.

This inductive type is the formal syntax of modal logic - the "language" in which
we express modal statements.

## The Constructors

**Primitive constructors** (cannot be defined in terms of others):

1. **bot**: Falsity (⊥)
   - The always-false proposition
   - Bottom of the truth lattice
   - Used to define negation: ¬φ ≡ φ → ⊥

2. **var n**: Propositional variable (typically written p, q, r, ...)
   - Atomic propositions (basic facts)
   - Indexed by natural numbers for infinite supply
   - Examples: "it is raining" (var 0), "the door is open" (var 1)
   - Semantics: truth value assigned by valuation

3. **and φ ψ**: Conjunction (φ ∧ ψ)
   - "Both φ and ψ"
   - True when both conjuncts are true
   - Commutative and associative

4. **impl φ ψ**: Implication (φ → ψ)
   - "If φ then ψ"
   - Classical implication (material conditional)
   - False only when φ is true and ψ is false
   - NOT intuitionistic implication

5. **box φ**: Necessity (□φ)
   - THE modal operator that makes this modal logic
   - "Necessarily φ" or "φ is necessary"
   - Semantic meaning: "φ is true at all accessible worlds"
   - Different interpretations:
     * Epistemic: "it is known that φ"
     * Temporal: "φ always holds" (in the future)
     * Deontic: "φ is obligatory"
     * Alethic: "φ is necessarily true"

## Mathematical Properties

**Well-founded**: The inductive definition makes formulas well-founded, enabling:
- Structural induction (prove property for all formulas)
- Structural recursion (define functions on formulas)
- Decidability (many properties become decidable)

**Countably infinite**: There are countably many formulas because:
- Countably many variables (indexed by ℕ)
- Finite number of constructors
- Finite branching at each step

**Abstract syntax**: This is a SYNTAX TREE, not a string
- No parsing ambiguity (fully parenthesized by construction)
- Direct manipulation without parsing
- Perfect for formal proofs
-/
inductive Form : Type
  | bot                : Form        -- ⊥ (falsity)
  | var  (n : Nat)     : Form        -- pₙ (propositional variable)
  | and  (φ ψ : Form)  : Form        -- φ ⋏ ψ (conjunction)
  | impl (φ ψ : Form)  : Form        -- φ ⟹ ψ (implication)
  | box  (φ : Form)    : Form        -- □φ (necessity)
deriving Repr, DecidableEq, Inhabited

------------------------------------------------------------------------------
-- § 1.1. Notation
-- Use `open BasicModal` to activate these in other files.
-- Note: □, ⊃, & and the modal derived operators are declared in Derived.lean.
------------------------------------------------------------------------------

/-- Conjunction: φ ⋏ ψ (alternative to &, active via `open BasicModal`) -/
scoped infixl:70 " ⋏ " => Form.and

/-- Implication: φ ⟹ ψ (alternative to ⊃, active via `open BasicModal`) -/
scoped infixr:60 " ⟹ " => Form.impl

/-- Propositional variable: p[n] -/
scoped notation "p[" n "]" => Form.var n

------------------------------------------------------------------------------
-- § 2. Complexity and Size Measures
------------------------------------------------------------------------------

/--
**Structural complexity** of a formula: total number of connectives.

This measure counts all constructors (including variables and ⊥), giving
the size of the syntax tree.

**Properties**:
- `complexity bot = 1`
- `complexity (var n) = 1`
- `complexity (φ ∧ ψ) = 1 + complexity φ + complexity ψ`
- Always positive
- Strictly increases with compound formulas

**Applications**:
- Termination proofs (induction on complexity)
- Algorithm analysis (complexity bounds)
- Filtration construction (restrict to bounded complexity)
-/
def complexity : Form → Nat
  | Form.bot => 1
  | Form.var _ => 1
  | Form.and φ ψ => 1 + complexity φ + complexity ψ
  | Form.impl φ ψ => 1 + complexity φ + complexity ψ
  | Form.box φ => 1 + complexity φ

/--
**Modal depth**: maximum nesting of box operators.

Counts the deepest level of modal nesting in a formula.

**Properties**:
- `modalDepth bot = 0`
- `modalDepth (var n) = 0`
- `modalDepth (φ ∧ ψ) = max (modalDepth φ) (modalDepth ψ)`
- `modalDepth (□φ) = 1 + modalDepth φ`

**Applications**:
- Characterizing modal complexity
- Finite model property (formulas of depth n need frames of size ≤ 2^n)
- Filtration bounds
-/
def modalDepth : Form → Nat
  | Form.bot => 0
  | Form.var _ => 0
  | Form.and φ ψ => max (modalDepth φ) (modalDepth ψ)
  | Form.impl φ ψ => max (modalDepth φ) (modalDepth ψ)
  | Form.box φ => 1 + modalDepth φ

/--
**Variable set**: all propositional variables occurring in a formula.

Collects the set of all variable indices that appear in the formula.

**Applications**:
- Determining which valuations matter
- Interpolation theorems (common variables)
- Substitution operations
-/
def vars : Form → Finset Nat
  | Form.bot => ∅
  | Form.var n => {n}
  | Form.and φ ψ => vars φ ∪ vars ψ
  | Form.impl φ ψ => vars φ ∪ vars ψ
  | Form.box φ => vars φ

/--
**Subformula set**: all subformulas of a formula.

Returns the set of all formulas that appear as sub-trees.

**Properties**:
- φ is always a subformula of itself
- Subformulas are closed under taking subformulas (transitive)
- Used in filtration and tableau constructions

**Applications**:
- Filtration (bound model size)
- Tableau method (systematic proof search)
- Complexity analysis
-/
def subformulas : Form → List Form
  | φ@Form.bot => [φ]
  | φ@(Form.var _) => [φ]
  | φ@(Form.and ψ χ) => φ :: (subformulas ψ ++ subformulas χ)
  | φ@(Form.impl ψ χ) => φ :: (subformulas ψ ++ subformulas χ)
  | φ@(Form.box ψ) => φ :: subformulas ψ

------------------------------------------------------------------------------
-- § 3. Decidability Instances
------------------------------------------------------------------------------

/--
Decidable equality for formulas.

This is derived automatically, but we make it explicit for documentation.
Formula equality is decidable because:
1. Finite constructors
2. Each constructor has decidable sub-components
3. Natural number equality is decidable
-/
instance : DecidableEq Form := inferInstance

/--
Decidable membership in the variable set.

Given a variable n and formula φ, we can decide if n ∈ vars φ.
-/
instance (n : Nat) (φ : Form) : Decidable (n ∈ vars φ) := by
  infer_instance

/--
Decidable subformula relation (for lists).

We can decide if ψ appears in the subformula list of φ.
-/
instance (ψ φ : Form) : Decidable (ψ ∈ subformulas φ) := by
  infer_instance

------------------------------------------------------------------------------
-- § 4. Basic Properties
------------------------------------------------------------------------------

/--
Complexity is always positive.

Every formula has at least complexity 1.
-/
theorem complexity_pos (φ : Form) : 0 < complexity φ := by
  cases φ <;> simp [complexity]

/--
Modal depth is bounded by complexity.

The modal depth never exceeds the total complexity.
-/
theorem modalDepth_le_complexity (φ : Form) : modalDepth φ ≤ complexity φ := by
  induction φ with
  | bot => simp [modalDepth, complexity]
  | var _ => simp [modalDepth, complexity]
  | and φ ψ ihφ ihψ =>
      simp [modalDepth, complexity]
      omega
  | impl φ ψ ihφ ihψ =>
      simp [modalDepth, complexity]
      omega
  | box φ ih =>
      simp [modalDepth, complexity]
      omega

/--
Variables in subformulas are subset of original variables.

If ψ is a subformula of φ, then vars ψ ⊆ vars φ.
-/
theorem vars_subformula (φ : Form) (ψ : Form) (h : ψ ∈ subformulas φ) :
    vars ψ ⊆ vars φ := by
  induction φ with
  | bot =>
      rw [subformulas] at h
      simp at h
      rw [h]
  | var n =>
      rw [subformulas] at h
      simp at h
      rw [h]
  | and φ₁ φ₂ ih₁ ih₂ | impl φ₁ φ₂ ih₁ ih₂ =>
      rw [subformulas] at h
      simp only [List.mem_cons] at h
      rcases h with heq | hmem
      · rw [heq]
      · rw [vars]
        have : ψ ∈ subformulas φ₁ ∨ ψ ∈ subformulas φ₂ := List.mem_append.mp hmem
        rcases this with h1 | h2
        · have := ih₁ h1
          exact Finset.Subset.trans this Finset.subset_union_left
        · have := ih₂ h2
          exact Finset.Subset.trans this Finset.subset_union_right
  | box φ ih =>
      rw [subformulas] at h
      simp only [List.mem_cons] at h
      rcases h with heq | hmem
      · rw [heq]
      · exact ih hmem

/--
Every formula is a subformula of itself.
-/
theorem mem_subformulas_self (φ : Form) : φ ∈ subformulas φ := by
  cases φ <;> simp [subformulas]

/--
Complexity of subformulas is strictly smaller.

If ψ is a proper subformula of φ (not equal to φ), then complexity ψ < complexity φ.
-/
theorem complexity_subformula_lt (φ ψ : Form)
    (h : ψ ∈ subformulas φ) (hne : ψ ≠ φ) :
    complexity ψ < complexity φ := by
  induction φ with
  | bot =>
      rw [subformulas] at h
      simp at h
      contradiction
  | var _ =>
      rw [subformulas] at h
      simp at h
      contradiction
  | and φ₁ φ₂ ih₁ ih₂ | impl φ₁ φ₂ ih₁ ih₂ =>
      rw [subformulas] at h
      simp only [List.mem_cons] at h
      rcases h with heq | hmem
      · contradiction
      · rw [complexity]
        have : ψ ∈ subformulas φ₁ ∨ ψ ∈ subformulas φ₂ := List.mem_append.mp hmem
        rcases this with h1 | h2
        · by_cases heq : ψ = φ₁
          · rw [heq]; omega
          · have := ih₁ h1 heq
            omega
        · by_cases heq : ψ = φ₂
          · rw [heq]; omega
          · have := ih₂ h2 heq
            omega
  | box φ ih =>
      rw [subformulas] at h
      simp only [List.mem_cons] at h
      rcases h with heq | hmem
      · contradiction
      · rw [complexity]
        by_cases heq : ψ = φ
        · rw [heq]; omega
        · have := ih hmem heq
          omega

------------------------------------------------------------------------------
-- § 5. Substitution
------------------------------------------------------------------------------

/--
**Substitution**: Replace all occurrences of variable n with formula ψ.

`subst φ n ψ` replaces every occurrence of (var n) in φ with ψ.

**Properties**:
- Captures the usual substitution from logic
- Preserves structure (respects all connectives)
- Used in axiom schemas and uniform substitution

**Example**:
- `subst (var 0 ∧ var 1) 0 (□(var 2))` = `□(var 2) ∧ var 1`
-/
def subst : Form → Nat → Form → Form
  | Form.bot, _, _ => Form.bot
  | Form.var m, n, ψ => if m = n then ψ else Form.var m
  | Form.and φ₁ φ₂, n, ψ => Form.and (subst φ₁ n ψ) (subst φ₂ n ψ)
  | Form.impl φ₁ φ₂, n, ψ => Form.impl (subst φ₁ n ψ) (subst φ₂ n ψ)
  | Form.box φ, n, ψ => Form.box (subst φ n ψ)

/--
Substitution complexity bound.

The complexity after substitution is at most the original complexity times
the complexity of the substituted formula.
-/
theorem subst_complexity_le (φ : Form) (n : Nat) (ψ : Form) :
    complexity (subst φ n ψ) ≤ complexity φ * complexity ψ := by
  induction φ with
  | bot =>
      simp [subst, complexity]
      have : 0 < complexity ψ := complexity_pos ψ
      omega
  | var m =>
      simp [subst, complexity]
      split
      · -- m = n, we substitute ψ
        omega
      · -- m ≠ n, complexity stays 1
        have : 0 < complexity ψ := complexity_pos ψ
        aesop
  | and φ₁ φ₂ ih₁ ih₂ | impl φ₁ φ₂ ih₁ ih₂ =>
      simp [subst, complexity]
      have cψ : 0 < complexity ψ := complexity_pos ψ
      have cφ₁ : 0 < complexity φ₁ := complexity_pos φ₁
      have cφ₂ : 0 < complexity φ₂ := complexity_pos φ₂
      calc 1 + complexity (subst φ₁ n ψ) + complexity (subst φ₂ n ψ)
          ≤ 1 + complexity φ₁ * complexity ψ + complexity φ₂ * complexity ψ := by omega
        _ ≤ complexity ψ + complexity φ₁ * complexity ψ + complexity φ₂ * complexity ψ := by omega
        _ = (1 + complexity φ₁ + complexity φ₂) * complexity ψ := by ring
  | box φ ih =>
      simp [subst, complexity]
      have cψ : 0 < complexity ψ := complexity_pos ψ
      have cφ : 0 < complexity φ := complexity_pos φ
      calc 1 + complexity (subst φ n ψ)
          ≤ 1 + complexity φ * complexity ψ := by omega
        _ ≤ complexity ψ + complexity φ * complexity ψ := by omega
        _ = (1 + complexity φ) * complexity ψ := by ring

end BasicModal
