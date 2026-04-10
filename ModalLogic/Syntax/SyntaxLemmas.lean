/-
Copyright (c) 2025 Huub Vromen.
Improved and modularized version
-/

import ModalLogic.Syntax.BasicLemmas

namespace BasicModal

--open Modal
open ProofK

/-!
# Derived Rules for Hilbert-Style Modal Logic K

## Motivation

**The Problem with Bare Hilbert Systems**: Hilbert-style proof systems have very few
primitive rules (axioms + modus ponens + necessitation), making them elegant but
painful to work with directly. Even simple proofs become extremely tedious.

**The Solution**: Derive a rich collection of **meta-theorems** (provable rules) that
allow more natural reasoning. This file is that toolkit.

## What This File Provides

A comprehensive library of derived rules organized by topic:
1. **Structural rules**: Identity, weakening
2. **Implication rules**: Cut, hypothetical syllogism, permutation
3. **Conjunction rules**: Introduction, elimination, distribution
4. **Negation rules**: Contraposition, double negation, De Morgan's laws
5. **Contradiction rules**: Ex falso, law of non-contradiction
6. **Modal rules**: Box-diamond duality, box monotonicity

## Design Philosophy

**Progressive abstraction**: Early lemmas are proven from axioms directly. Later lemmas
build on earlier ones, creating layers of abstraction.

**Naming conventions**:
- `identity`: identity/reflexivity (from BasicLemmas.lean)
- `cut`, `imp_comp`: transitivity/composition
- `imp_*`: operations on implications
- `and_*`: operations on conjunctions
- `*_equiv_*`: logical equivalences
- `box_*`, `dia_*`: modal operations
-/

------------------------------------------------------------------------------
-- § 1. Basic Structural Rules
------------------------------------------------------------------------------

/--
**Truth**: The formula ⊤ₘ (defined as ∼⊥ₘ) is provable.
-/
@[simp] lemma prtrue {Γ : Ctx} : ProofK Γ (∼⊥ₘ) := identity



------------------------------------------------------------------------------
-- § 2. Implication Rules
------------------------------------------------------------------------------

/--
**Cut/Transitivity**: Compose implications.

From φ ⊃ ψ and ψ ⊃ χ, derive φ ⊃ χ.
-/
lemma cut {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (φ ⊃ ψ) → ProofK Γ (ψ ⊃ χ) → ProofK Γ (φ ⊃ χ) := by
  intro h1 h2
  have : ProofK Γ (φ ⊃ (ψ ⊃ χ)) :=
    mp (pl1 : ProofK Γ ((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)))) h2
  exact mp (mp (pl2 : ProofK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))) this) h1

/--
**K-introduction**: Prepend an antecedent using PL1.

From φ, derive ψ ⊃ φ.
-/
lemma k_intro {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ φ → ProofK Γ (ψ ⊃ φ) := by
  intro h
  exact mp (pl1 : ProofK Γ (φ ⊃ (ψ ⊃ φ))) h

/--
**Implication composition**: Curried form of cut.

From ψ ⊃ χ and φ ⊃ ψ, derive φ ⊃ χ.
-/
lemma imp_comp {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (ψ ⊃ χ) → ProofK Γ (φ ⊃ ψ) → ProofK Γ (φ ⊃ χ) := by
  intro hψχ hφψ
  have s1 : ProofK Γ (φ ⊃ (ψ ⊃ χ)) :=
    mp (pl1 : ProofK Γ ((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)))) hψχ
  have s2 : ProofK Γ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)) :=
    mp (pl2 : ProofK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))) s1
  exact mp s2 hφψ

/--
**Curried hypothetical syllogism**: Object-level composition.

⊢ (ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))
-/
lemma imp_comp_curried {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ ((ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))) := by
  have t1 : ProofK Γ ((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ))) := pl1
  have t2 : ProofK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))) := pl2
  have k : ProofK Γ (((φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
                   ⊃ ((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))) := pl1
  have t3 : ProofK Γ ((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))) := mp k t2
  have p2 : ProofK Γ (((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))
                    ⊃ (((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)))
                       ⊃ ((ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))))) := pl2
  have t4 : ProofK Γ (((ψ ⊃ χ) ⊃ (φ ⊃ (ψ ⊃ χ)))
                    ⊃ ((ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ)))) := mp p2 t3
  exact mp t4 t1

/--
**Converse of deduction**: From φ ⊃ ψ derive ψ in context φ.
-/
lemma conv_deduction {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (φ ⊃ ψ) → ProofK (Γ ∪ₛ φ) ψ := by
  intro h; exact mp (weaken_insert_right h) of_insert

/--
**Hypothetical syllogism (type 1)**: Distribution-like rule.

⊢ (ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))
-/
lemma hs1 {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ ((ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))) := by
  exact mp (mp pl2 (mp pl1 pl2)) pl1

/--
**Modus ponens combinator**: φ ⊃ ((φ ⊃ ψ) ⊃ ψ)
-/
lemma likemp {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (φ ⊃ ((φ ⊃ ψ) ⊃ ψ)) := by
  exact mp (mp hs1 (mp pl2 identity)) pl1

/--
**Swap nested implications**: Permute the order of antecedents.

From φ ⊃ (ψ ⊃ χ) derive ψ ⊃ (φ ⊃ χ).
-/
lemma imp_switch {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (φ ⊃ (ψ ⊃ χ)) → ProofK Γ (ψ ⊃ (φ ⊃ χ)) := by
  intro h1; exact mp (mp pl2 (mp pl1 (mp pl2 h1))) pl1

/--
**Object-level antecedent swap**: Axiomatic form of `imp_switch`.

⊢ (φ ⊃ (ψ ⊃ χ)) ⊃ (ψ ⊃ (φ ⊃ χ))
-/
lemma imp_switch_ax {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ ((φ ⊃ (ψ ⊃ χ)) ⊃ (ψ ⊃ (φ ⊃ χ))) := by
  exact mp (mp pl2 (cut pl2 hs1)) (mp pl1 pl1)

/--
**Hypothetical syllogism (type 2)**: Reverse form.

⊢ (φ ⊃ ψ) ⊃ ((ψ ⊃ χ) ⊃ (φ ⊃ χ))
-/
lemma hs2 {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ ((φ ⊃ ψ) ⊃ ((ψ ⊃ χ) ⊃ (φ ⊃ χ))) := by
  exact mp imp_switch_ax hs1

/--
**Strengthen antecedent**: From φ ⊃ χ derive φ ⊃ (ψ ⊃ χ).
-/
lemma imp_if_imp_imp {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (φ ⊃ χ) → ProofK Γ (φ ⊃ (ψ ⊃ χ)) := by
  intro h1; exact mp (mp pl2 (mp pl1 pl1)) h1

/--
**Curried cut**: Compose with a curried implication.
-/
lemma cut1 {Γ : Ctx} {φ ψ χ θ : Form} :
    ProofK Γ (θ ⊃ (φ ⊃ ψ)) → ProofK Γ (ψ ⊃ χ) → ProofK Γ (θ ⊃ (φ ⊃ χ)) := by
  intro h1 h2; exact cut h1 (mp pl2 (mp pl1 h2))

/--
**Compose with first argument**: Another variant of composition.
-/
lemma cut2 {Γ : Ctx} {φ ψ χ θ : Form} :
    ProofK Γ (φ ⊃ ψ) → ProofK Γ (θ ⊃ (ψ ⊃ χ)) → ProofK Γ (θ ⊃ (φ ⊃ χ)) := by
  intro h1 h2; exact imp_switch (cut h1 (imp_switch h2))

/--
**Contraction**: φ ⊃ (φ ⊃ ψ) implies φ ⊃ ψ.
-/
lemma double_imp {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ ((φ ⊃ (φ ⊃ ψ)) ⊃ (φ ⊃ ψ)) := by
  exact mp pl2 (imp_switch identity)

/--
**Equivalence for nested implications**: Collapse/expand nested implications.
-/
lemma imp_imp_iff_imp {Γ : Ctx} {θ φ ψ : Form} :
    ProofK Γ (θ ⊃ (φ ⊃ (φ ⊃ ψ))) ↔ ProofK Γ (θ ⊃ (φ ⊃ ψ)) := by
  constructor
  · intro h1; exact cut h1 double_imp
  · intro h1; exact cut h1 pl1

/--
**Swap nested antecedents**: Exchange rule for triply-nested implications.
-/
lemma imp_shift {Γ : Ctx} {θ φ ψ χ : Form} :
    ProofK Γ (θ ⊃ (φ ⊃ (ψ ⊃ χ))) ↔ ProofK Γ (θ ⊃ (ψ ⊃ (φ ⊃ χ))) := by
  constructor
  all_goals intro h1; exact cut h1 (cut2 pl1 pl2)

------------------------------------------------------------------------------
-- § 3. Conjunction Rules
------------------------------------------------------------------------------

/-- Internal helper for conjunction elimination. -/
private lemma left_and_imp {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (ψ ⊃ ((φ & ψ) ⊃ χ)) → ProofK Γ ((φ & ψ) ⊃ χ) := by
  intro h1; exact mp double_imp (cut pl6 h1)

/--
**Conjunction to implication**: Convert conjunction in antecedent to nested implication.

(φ & ψ) ⊃ χ ⇔ ψ ⊃ (φ ⊃ χ)
-/
lemma and_right_imp {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ ((φ & ψ) ⊃ χ) ↔ ProofK Γ (ψ ⊃ (φ ⊃ χ)) := by
  constructor
  · intro h1; exact mp (cut2 pl1 pl2) (cut1 pl4 h1)
  · intro h1; exact left_and_imp (cut2 pl5 h1)

/--
**Distribute implication over conjunction**: Function application to both conjuncts.
-/
lemma imp_and_and_imp {Γ : Ctx} {φ ψ χ θ : Form} :
    ProofK Γ ((φ ⊃ ψ) & (χ ⊃ θ)) → ProofK Γ ((φ & χ) ⊃ (ψ & θ)) := by
  intro h
  exact mp double_imp
    (cut (cut pl5 (mp pl5 h)) (cut2 (cut pl6 (mp pl6 h)) pl4))

/--
**Apply implication to conjunct**: Preserve one side, transform the other.
-/
lemma imp_and_imp {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (φ ⊃ ψ) → ProofK Γ ((χ & φ) ⊃ (χ & ψ)) := by
  intro h1; exact imp_and_and_imp (mp (mp pl4 identity) h1)

/--
**Conjunction with truth**: φ & ⊤ₘ ⇔ φ
-/
lemma phi_and_true {Γ : Ctx} {φ : Form} :
    ProofK Γ ((φ & ∼⊥ₘ) ⇔ φ) :=
  mp (mp pl4 pl5) (mp (imp_switch pl4) prtrue)

/--
**Commutativity of conjunction**: φ & ψ ⇔ ψ & φ
-/
lemma and_switch {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ ((φ & ψ) ⇔ (ψ & φ)) := by
  have hψ : ProofK Γ ((φ & ψ) ⊃ ψ) := pl6
  have hφ : ProofK Γ ((φ & ψ) ⊃ φ) := pl5
  have hintro₁ : ProofK Γ (ψ ⊃ (φ ⊃ (ψ & φ))) := pl4
  have dir₁_step : ProofK Γ ((φ & ψ) ⊃ (φ ⊃ (ψ & φ))) := cut hψ hintro₁
  have dir₁ : ProofK Γ ((φ & ψ) ⊃ (ψ & φ)) :=
    mp (mp (pl2 : ProofK Γ (((φ & ψ) ⊃ (φ ⊃ (ψ & φ)))
                   ⊃ (((φ & ψ) ⊃ φ) ⊃ ((φ & ψ) ⊃ (ψ & φ)))))
        dir₁_step) hφ
  have hφ' : ProofK Γ ((ψ & φ) ⊃ φ) := pl6
  have hψ' : ProofK Γ ((ψ & φ) ⊃ ψ) := pl5
  have hintro₂ : ProofK Γ (φ ⊃ (ψ ⊃ (φ & ψ))) := pl4
  have dir₂_step : ProofK Γ ((ψ & φ) ⊃ (ψ ⊃ (φ & ψ))) := cut hφ' hintro₂
  have dir₂ : ProofK Γ ((ψ & φ) ⊃ (φ & ψ)) :=
    mp (mp (pl2 : ProofK Γ (((ψ & φ) ⊃ (ψ ⊃ (φ & ψ)))
                   ⊃ (((ψ & φ) ⊃ ψ) ⊃ ((ψ & φ) ⊃ (φ & ψ)))))
        dir₂_step) hψ'
  exact mp (mp pl4 dir₁) dir₂

/--
**Associativity of conjunction**: (φ & ψ) & χ ⇔ φ & (ψ & χ)
-/
lemma and_assoc {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (((φ & ψ) & χ) ⇔ (φ & (ψ & χ))) := by
  exact
    mp (mp pl4 (mp double_imp (imp_imp_iff_imp.mp
      (cut (cut pl5 pl6) (cut2 pl6 (cut1 pl4 (imp_switch (cut (cut pl5 pl5) pl4))))))))
       (mp double_imp (imp_imp_iff_imp.mp (cut (cut pl6 pl5)
         (imp_switch (cut pl5 (cut1 pl4 (cut2 (cut pl6 pl6) pl4)))))))

------------------------------------------------------------------------------
-- § 4. Negation Rules
------------------------------------------------------------------------------

/--
**Double-negation elimination (DNE)**: ∼∼φ ⊃ φ

This is the characteristic axiom of classical logic.
-/
@[simp] lemma dne {Γ : Ctx} {φ : Form} :
    ProofK Γ (∼∼φ ⊃ φ) := by
  have h1 : ProofK Γ (φ ⊃ (φ ⊃ φ)) := pl1
  exact cut (cut pl1 (cut pl3 pl3)) (mp likemp h1)

/--
**Double-negation introduction (DNI)**: φ ⊃ ∼∼φ
-/
@[simp] lemma dni {Γ : Ctx} {φ : Form} :
    ProofK Γ (φ ⊃ ∼∼φ) := mp pl3 dne

/--
**Peirce's law variant** (derived): ((¬φ → ¬ψ) → ((¬φ → ψ) → φ))

This was formerly axiom PL3. It is now derived from PL1, PL2, and PL3
(contraposition). The proof uses contraposition and DNE: if ¬φ → ¬ψ and
¬φ → ψ, then from ¬φ we get both ψ and ¬ψ, contradiction, so ¬¬φ, and
by DNE, φ.
-/
lemma peirce_variant {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (((¬ₘφ) ⊃ (¬ₘψ)) ⊃ (((¬ₘφ) ⊃ ψ) ⊃ φ)) := by
  -- Step 1: (¬φ → ¬ψ) → ((¬φ → ψ) → (¬φ → φ)) via PL3 + hs1
  have step12 : ProofK Γ ((¬ₘφ ⊃ ¬ₘψ) ⊃ ((¬ₘφ ⊃ ψ) ⊃ (¬ₘφ ⊃ φ))) :=
    cut pl3 hs1
  -- Step 2: (¬φ → φ) → φ  (from ¬φ → φ, get ¬φ → ¬¬φ by dni, contract, apply dne)
  have nf_imp_f_imp_f : ProofK Γ ((¬ₘφ ⊃ φ) ⊃ φ) :=
    cut (cut (mp hs1 dni) double_imp) dne
  -- Combine: (¬φ → ¬ψ) → ((¬φ → ψ) → φ)
  exact cut1 step12 nf_imp_f_imp_f

/--
**Forward contraposition**: (φ ⊃ ψ) ⊃ (¬ψ ⊃ ¬φ)
-/
lemma contrapos_mp {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ ((φ ⊃ ψ) ⊃ (¬ₘψ ⊃ ¬ₘφ)) := by
  have h_dneφ : ProofK Γ (¬ₘ¬ₘφ ⊃ φ) := dne
  have h_dniψ : ProofK Γ (ψ ⊃ ¬ₘ¬ₘψ) := dni

  -- Step A: (φ ⊃ ψ) ⊃ (¬¬φ ⊃ ψ)
  have ic : ProofK Γ ((φ ⊃ ψ) ⊃ ((¬ₘ¬ₘφ ⊃ φ) ⊃ (¬ₘ¬ₘφ ⊃ ψ))) :=
    @imp_comp_curried Γ (¬ₘ¬ₘφ) φ ψ
  have ic_switched : ProofK Γ ((¬ₘ¬ₘφ ⊃ φ) ⊃ ((φ ⊃ ψ) ⊃ (¬ₘ¬ₘφ ⊃ ψ))) :=
    imp_switch ic
  have stepA : ProofK Γ ((φ ⊃ ψ) ⊃ (¬ₘ¬ₘφ ⊃ ψ)) := mp ic_switched h_dneφ

  -- Step B: (¬¬φ ⊃ ψ) ⊃ (¬¬φ ⊃ ¬¬ψ)
  have stepB : ProofK Γ ((¬ₘ¬ₘφ ⊃ ψ) ⊃ (¬ₘ¬ₘφ ⊃ ¬ₘ¬ₘψ)) :=
    mp (@imp_comp_curried Γ (¬ₘ¬ₘφ) ψ (¬ₘ¬ₘψ)) h_dniψ

  -- Step AB: (φ ⊃ ψ) ⊃ (¬¬φ ⊃ ¬¬ψ)
  have stepAB : ProofK Γ ((φ ⊃ ψ) ⊃ (¬ₘ¬ₘφ ⊃ ¬ₘ¬ₘψ)) :=
    imp_comp stepB stepA

  -- Step C: Apply PL3 to get (¬¬φ ⊃ ¬¬ψ) ⊃ (¬ψ ⊃ ¬φ)
  have pl3_inst : ProofK Γ ((¬ₘ¬ₘφ ⊃ ¬ₘ¬ₘψ) ⊃ (¬ₘψ ⊃ ¬ₘφ)) := pl3

  -- Final: (φ ⊃ ψ) ⊃ (¬ψ ⊃ ¬φ)
  exact imp_comp pl3_inst stepAB

/--
**Reverse contraposition**: (¬ψ ⊃ ¬φ) ⊃ (φ ⊃ ψ)
-/
lemma contrapos_mpr {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ ((¬ₘψ ⊃ ¬ₘφ) ⊃ (φ ⊃ ψ)) :=
  pl3

/--
**Contraposition equivalence**: (∼ψ ⊃ ∼φ) ⇔ (φ ⊃ ψ)
-/
lemma contrapos {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (∼ψ ⊃ ∼φ) ↔ ProofK Γ (φ ⊃ ψ) := by
  constructor
  · intro h1; exact mp pl3 h1
  · intro h1; exact mp (cut (cut (mp hs1 dni) (mp hs2 dne)) pl3) h1

/--
**Negation respects equivalence**: If φ ⇔ ψ, then ∼ψ ⇔ ∼φ.
-/
lemma iff_not {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (φ ⇔ ψ) → ProofK Γ (∼ψ ⇔ ∼φ) := by
  intro h1
  have h2 : ProofK Γ (φ ⊃ ψ) := mp pl5 h1
  have h3 : ProofK Γ (ψ ⊃ φ) := mp pl6 h1
  have hL : ProofK Γ (∼ψ ⊃ ∼φ) := contrapos.mpr h2
  have hR : ProofK Γ (∼φ ⊃ ∼ψ) := (contrapos (φ := ψ) (ψ := φ)).mpr h3
  exact mp (mp pl4 hL) hR

/--
**Symmetry of equivalence**: φ ⇔ ψ implies ψ ⇔ φ.
-/
lemma iff_symm {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (φ ⇔ ψ) → ProofK Γ (ψ ⇔ φ) := by
  intro h
  have h₁ : ProofK Γ (φ ⊃ ψ) := mp pl5 h
  have h₂ : ProofK Γ (ψ ⊃ φ) := mp pl6 h
  exact mp (mp pl4 h₂) h₁

------------------------------------------------------------------------------
-- § 5. Contradiction and Falsity
------------------------------------------------------------------------------

/--
**De Morgan's law**: ∼(φ & ψ) ⇔ (φ ⊃ ∼ψ)
-/
lemma demorgans {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (∼(φ & ψ)) ↔ ProofK Γ (φ ⊃ ∼ψ) := by
  constructor
  · intro h1; exact and_right_imp.mp (mp (contrapos.mpr (mp pl5 and_switch)) h1)
  · intro h1; exact mp (contrapos.mpr (mp pl5 and_switch)) (and_right_imp.mpr h1)

/--
**Law of non-contradiction**: ∼(φ & ∼φ) is provable.
-/
lemma not_contra {Γ : Ctx} {φ : Form} :
    ProofK Γ (∼(φ & ∼φ)) :=
  (demorgans (φ := φ) (ψ := ∼φ)).mpr (dni (φ := φ))

/--
**Non-contradiction equivalent to truth**: ∼(φ & ∼φ) ⇔ ⊤ₘ
-/
lemma not_contra_equiv_true {Γ : Ctx} {φ : Form} :
    ProofK Γ (∼(φ & ∼φ) ⇔ ⊤ₘ) :=
  mp (mp pl4 (mp pl1 prtrue)) (mp pl1 not_contra)

/--
**Contradiction equivalent to falsity**: (φ & ∼φ) ⇔ ⊥ₘ
-/
lemma contra_equiv_false {Γ : Ctx} {φ : Form} :
    ProofK Γ ((φ & ∼φ) ⇔ ⊥ₘ) := by
  let C : Form := φ & ∼φ
  have h1_raw : ProofK Γ (∼⊤ₘ ⇔ ∼∼C) := iff_not (φ := ∼C) (ψ := ⊤ₘ) not_contra_equiv_true
  have hAtoB : ProofK Γ (∼⊤ₘ ⊃ ∼∼C) := mp pl5 h1_raw
  have hBtoA : ProofK Γ (∼∼C ⊃ ∼⊤ₘ) := mp pl6 h1_raw
  have C_to_bot : ProofK Γ (C ⊃ ⊥ₘ) := by
    have nnBot_to_bot : ProofK Γ (∼∼⊥ₘ ⊃ ⊥ₘ) := dne (φ := ⊥ₘ)
    exact cut (cut (dni (φ := C)) hBtoA) nnBot_to_bot
  have bot_to_C : ProofK Γ (⊥ₘ ⊃ C) := by
    have bot_to_nnBot : ProofK Γ (⊥ₘ ⊃ ∼∼⊥ₘ) := dni (φ := ⊥ₘ)
    have nnC_to_C : ProofK Γ (∼∼C ⊃ C) := dne (φ := C)
    exact cut bot_to_nnBot (cut hAtoB nnC_to_C)
  exact mp (mp pl4 C_to_bot) bot_to_C

/--
**Ex falso quodlibet**: From falsity, anything follows: ⊥ₘ ⊃ ψ
-/
lemma explosion {Γ : Ctx} {ψ : Form} :
    ProofK Γ (⊥ₘ ⊃ ψ) := by
  apply contrapos.mp
  exact mp pl1 identity

/--
**From contradiction, anything**: (φ & ∼φ) ⊃ ψ
-/
lemma exfalso {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ ((φ & ∼φ) ⊃ ψ) :=
  cut not_contra explosion

/--
**Substitution under negation and conjunction**: Equivalence preservation.

If φ ⇔ ψ, then ∼(χ & φ) ⇔ ∼(χ & ψ).
-/
lemma not_and_subst {Γ : Ctx} {φ ψ χ : Form} :
    ProofK Γ (φ ⇔ ψ) → (ProofK Γ (∼(χ & φ)) ↔ ProofK Γ (∼(χ & ψ))) := by
  intro h1
  constructor
  · intro h2
    have hχnφ : ProofK Γ (χ ⊃ ∼φ) := (demorgans (φ := χ) (ψ := φ)).mp h2
    have hψφ : ProofK Γ (ψ ⊃ φ) := mp pl6 h1
    have hnφnψ : ProofK Γ (∼φ ⊃ ∼ψ) := (contrapos (φ := ψ) (ψ := φ)).mpr hψφ
    have hχnψ : ProofK Γ (χ ⊃ ∼ψ) := cut hχnφ hnφnψ
    exact (demorgans (φ := χ) (ψ := ψ)).mpr hχnψ
  · intro h2
    have hχnψ : ProofK Γ (χ ⊃ ∼ψ) := (demorgans (φ := χ) (ψ := ψ)).mp h2
    have hφψ : ProofK Γ (φ ⊃ ψ) := mp pl5 h1
    have hnψnφ : ProofK Γ (∼ψ ⊃ ∼φ) := contrapos.mpr hφψ
    have hχnφ : ProofK Γ (χ ⊃ ∼φ) := cut hχnψ hnψnφ
    exact (demorgans (φ := χ) (ψ := φ)).mpr hχnφ

------------------------------------------------------------------------------
-- § 6. Modal Rules
------------------------------------------------------------------------------

/--
**Box monotonicity**: If φ ⊃ ψ is provable, then □φ ⊃ □ψ is provable.
-/
@[simp] lemma box_mono {Γ : Ctx} {φ ψ : Form} :
    ProofK Γ (φ ⊃ ψ) → ProofK Γ (□φ ⊃ □ψ) := by
  intro h
  exact mp (kdist : ProofK Γ (□(φ ⊃ ψ) ⊃ (□φ ⊃ □ψ))) (nec h)

/--
**Box and double negation**: ∼□φ ⇔ ∼□∼∼φ
-/
lemma box_dn {Γ : Ctx} {φ : Form} :
    ProofK Γ (∼(□ φ) ⇔ ∼(□ (∼(∼φ)))) := by
  exact mp (mp pl4 (contrapos.mpr (mp kdist (nec dne))))
           (contrapos.mpr (mp kdist (nec dni)))

/--
**Box-Diamond duality 1**: □φ ⇔ ∼◇∼φ

Necessity equals impossibility of negation.
-/
@[simp] lemma dual_equiv1 {Γ : Ctx} {φ : Form} :
    ProofK Γ (□ φ ⇔ ∼(◇ (∼φ))) := by
  exact mp (mp pl4 (cut (contrapos.mp (mp pl6 box_dn)) dni))
           (cut dne (contrapos.mp (mp pl5 box_dn)))

/--
**Box-Diamond duality 2**: ∼□∼φ ⇔ ◇φ

Non-necessity equals possibility.
-/
@[simp] lemma dual_equiv2 {Γ : Ctx} {φ : Form} :
    ProofK Γ (∼(□ (∼φ)) ⇔ ◇ φ) := by
  exact mp (mp pl4 identity) identity

/--
**Box to not-diamond**: □α ⊃ ¬◇¬α
-/
lemma box_to_not_dia {Γ : Ctx} {α : Form} :
    ProofK Γ (□ α ⊃ ¬ₘ(◇ (¬ₘα))) := by
  exact mp pl5 (dual_equiv1 (φ := α))

/--
**Not-diamond to box**: ¬◇¬α ⊃ □α
-/
lemma not_dia_to_box {Γ : Ctx} {α : Form} :
    ProofK Γ (¬ₘ(◇ (¬ₘα)) ⊃ □ α) := by
  exact mp pl6 (dual_equiv1 (φ := α))

/--
**Not-box to diamond**: ¬□¬α ⊃ ◇α
-/
lemma not_box_to_dia {Γ : Ctx} {α : Form} :
    ProofK Γ (¬ₘ(□ (¬ₘα)) ⊃ ◇ α) := by
  exact mp pl5 (dual_equiv2 (φ := α))

/--
**Diamond to not-box**: ◇α ⊃ ¬□¬α
-/
lemma dia_to_not_box {Γ : Ctx} {α : Form} :
    ProofK Γ (◇ α ⊃ ¬ₘ(□ (¬ₘα))) := by
  exact mp pl6 (dual_equiv2 (φ := α))

/-- **Not-box implies diamond-neg**: ¬□φ ⊃ ◇¬φ -/
lemma not_box_to_dia_neg {Γ : Ctx} {φ : Form} :
    ProofK Γ (∼(□φ) ⊃ ◇(∼φ)) := by
  -- ◇¬φ ⇔ ¬□¬¬φ by duality
  have h1 : ProofK Γ (◇(∼φ) ⇔ ∼(□(∼(∼φ)))) := dual_equiv2
  -- ¬□¬¬φ ⊃ ◇¬φ
  have h2 : ProofK Γ (∼(□(∼(∼φ))) ⊃ ◇(∼φ)) := mp pl6 h1
  -- □φ ⊃ □¬¬φ (box_mono with dni)
  have h3 : ProofK Γ (□φ ⊃ □(∼(∼φ))) := box_mono dni
  -- ¬□¬¬φ ⊃ ¬□φ by contraposition
  have h4 : ProofK Γ (∼(□(∼(∼φ))) ⊃ ∼(□φ)) := contrapos.mpr h3
  -- □¬¬φ ⊃ □φ via box_mono + double negation elimination
  have h5 : ProofK Γ (□(∼(∼φ)) ⊃ □φ) := box_mono dne
  -- ¬□φ ⊃ ¬□¬¬φ by contraposition
  have h6 : ProofK Γ (∼(□φ) ⊃ ∼(□(∼(∼φ)))) := contrapos.mpr h5
  exact cut h6 h2

/-- **Diamond implies not-box**: ◇¬φ ⊃ ¬□φ -/
lemma dia_neg_to_not_box {Γ : Ctx} {φ : Form} :
    ProofK Γ (◇(∼φ) ⊃ ∼(□φ)) := by
  -- ◇¬φ ⇔ ¬□¬¬φ by duality
  have h1 : ProofK Γ (◇(∼φ) ⇔ ∼(□(∼(∼φ)))) := dual_equiv2
  -- ◇¬φ ⊃ ¬□¬¬φ
  have h2 : ProofK Γ (◇(∼φ) ⊃ ∼(□(∼(∼φ)))) := mp pl5 h1
  -- □φ ⊃ □¬¬φ
  have h3 : ProofK Γ (□φ ⊃ □(∼(∼φ))) := box_mono dni
  -- ¬□¬¬φ ⊃ ¬□φ by contraposition
  have h4 : ProofK Γ (∼(□(∼(∼φ))) ⊃ ∼(□φ)) := contrapos.mpr h3
  exact cut h2 h4

/-- **Box of not-box implies not-diamond**: □¬□φ ⊃ ¬◇□φ -/
lemma box_not_box_to_not_dia {Γ : Ctx} {φ : Form} :
    ProofK Γ (□(∼(□φ)) ⊃ ∼(◇(□φ))) := by
  -- □¬□φ ⇔ ¬◇¬¬□φ by duality
  have h1 : ProofK Γ (□(∼(□φ)) ⇔ ∼(◇(∼(∼(□φ))))) := dual_equiv1
  have h2 : ProofK Γ (□(∼(□φ)) ⊃ ∼(◇(∼(∼(□φ))))) := mp pl5 h1
  -- ◇□φ ⊃ ◇¬¬□φ by diamond monotonicity with dni
  have h3 : ProofK Γ (◇(□φ) ⊃ ◇(∼(∼(□φ)))) := by
    have : ProofK Γ (□φ ⊃ ∼(∼(□φ))) := dni
    have contra_step : ProofK Γ (∼(∼(∼(□φ))) ⊃ ∼(□φ)) := contrapos.mpr this
    have boxed : ProofK Γ (□(∼(∼(∼(□φ)))) ⊃ □(∼(□φ))) := box_mono contra_step
    exact contrapos.mpr boxed
  -- ¬◇¬¬□φ ⊃ ¬◇□φ by contraposition
  have h4 : ProofK Γ (∼(◇(∼(∼(□φ)))) ⊃ ∼(◇(□φ))) := contrapos.mpr h3
  exact cut h2 h4

end BasicModal
