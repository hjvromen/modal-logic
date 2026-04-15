/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Largest Filtration

This file defines the **largest filtration** — the coarsest (most permissive)
relation on subformula equivalence classes that still yields a valid filtration.

## Definitions

Given a formula φ, a model (F, v), and the subformula set Σ = Sub(φ), the
**largest filtration relation** on equivalence classes is:

  [x] R_L [y]  iff  ∀ □ψ ∈ Σ, forces(x, □ψ) → forces(y, ψ)

## Main Results

- `largestFiltRel`: The largest filtration relation
- `largestFiltRel_well_defined`: Independence of representative choice
- `smallestFilt_le_largestFilt`: The smallest filtration is contained in the largest
- `largestFiltrationFrame`: The largest filtration frame
- `largestFiltration_lemma`: Truth preservation (filtration lemma) for R_L
- `largestFiltration_finite`: The largest filtration frame is finite
- `largestFiltrationFrame_card_le`: Cardinality bound (≤ 2^|Sub(φ)|)

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §2.3
- Chellas, *Modal Logic: An Introduction*, Ch. 5
-/

import Mathlib
import ModalLogic.Semantics.DecidabilityMore

namespace Modal
open Modal
open BasicModal

/-!
## § 1. The Largest Filtration Relation
-/

/-- The largest filtration relation: [x] R_L [y] iff for all □ψ ∈ Sub(φ),
    forces(x, □ψ) implies forces(y, ψ). This is the largest relation that
    can serve as a filtration (i.e., contains the smallest filtration and
    satisfies the filtration lemma). -/
def largestFiltRel (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (qx qy : (filtrationFrame F v φ).states) : Prop :=
  ∀ ψ, (Form.box ψ) ∈ subformulas φ →
    forces F v qx.out (Form.box ψ) → forces F v qy.out ψ

/-!
## § 2. Well-Definedness
-/

/-
The largest filtration relation is well-defined: it is independent of the
    choice of representatives for the equivalence classes. This follows because
    subformula equivalence preserves truth of all formulas in Sub(φ).
-/
lemma largestFiltRel_well_defined (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x₁ x₂ y₁ y₂ : F.states)
    (hx : subfmlEquiv F v φ x₁ x₂) (hy : subfmlEquiv F v φ y₁ y₂)
    (hR : ∀ ψ, (Form.box ψ) ∈ subformulas φ →
      forces F v x₁ (Form.box ψ) → forces F v y₁ ψ) :
    ∀ ψ, (Form.box ψ) ∈ subformulas φ →
      forces F v x₂ (Form.box ψ) → forces F v y₂ ψ := by
  intro ψ hψ hψ';
  exact ( hy ψ ( box_subformula_imp_subformula hψ ) ) |>.mp ( hR ψ hψ ( ( hx ( Form.box ψ ) hψ ) |>.mpr hψ' ) )

/-!
## § 3. Containment: Smallest ⊆ Largest
-/

/-
The smallest filtration relation is contained in the largest filtration
    relation: if [x] R_s [y], then [x] R_L [y].

    Proof: If R_s([x],[y]), there exist x' ∈ [x], y' ∈ [y] with R(x',y').
    For □ψ ∈ Sub(φ) with forces([x].out, □ψ): since [x].out ~ x', forces(x', □ψ);
    then R(x', y') gives forces(y', ψ); and y' ~ [y].out gives forces([y].out, ψ).
-/
lemma smallestFilt_le_largestFilt (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (qx qy : (filtrationFrame F v φ).states)
    (hrel : (filtrationFrame F v φ).rel qx qy) :
    largestFiltRel F v φ qx qy := by
  obtain ⟨x', y', hx', hy', hxy'⟩ : ∃ x' y', subfmlEquiv F v φ qx.out x' ∧ subfmlEquiv F v φ qy.out y' ∧ F.rel x' y' := by
    rw [ ← Quotient.out_eq qx, ← Quotient.out_eq qy ] at hrel; exact hrel;
  intro ψ hψ;
  have := box_subformula_imp_subformula hψ;
  have := hx' ( □ ψ ) hψ;
  have := hy' ψ ‹_›; aesop;

/-!
## § 4. The Largest Filtration Frame
-/

/-- The largest filtration frame: same equivalence classes as the smallest
    filtration, but with the largest filtration relation R_L. -/
noncomputable def largestFiltrationFrame (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Frame where
  states := (filtrationFrame F v φ).states
  rel := largestFiltRel F v φ

/-!
## § 5. Filtration Lemma for the Largest Filtration
-/

/-- Quotient representatives are subformula-equivalent to the original world. -/
lemma mk_out_equiv (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x : F.states) : subfmlEquiv F v φ x (Quotient.mk (subfmlSetoid F v φ) x).out :=
  subfmlEquiv_symm (Quotient.mk_out (s := subfmlSetoid F v φ) x)

/-
**Filtration Lemma for the Largest Filtration**: For any subformula ψ of φ,
    truth in the original model is equivalent to truth in the largest filtration
    model.

    The proof is by induction on ψ:
    - Propositional cases: identical to the smallest filtration.
    - □ψ (→): If forces(x, □ψ) and R_L([x], q), then by definition of R_L
      (with □ψ ∈ Sub(φ)), forces(q.out, ψ). By IH, forces_L(q, ψ).
    - □ψ (←): By contrapositive. If ¬forces(x, □ψ), then ∃y, R(x,y) ∧ ¬forces(y,ψ).
      R(x,y) gives R_s([x],[y]) ⊆ R_L([x],[y]). By IH, ¬forces_L([y], ψ).
      So ¬forces_L([x], □ψ).
-/
theorem largestFiltration_lemma (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x : F.states) (ψ : Form) (hψ : ψ ∈ subformulas φ) :
    forces F v x ψ ↔
      forces (largestFiltrationFrame F v φ) (filtrationVal F v φ)
        (Quotient.mk (subfmlSetoid F v φ) x) ψ := by
  induction' ψ with ψ hψ generalizing x;
  · aesop;
  · simp [forces, filtrationVal, hψ];
  · have h₁' := and_subformula_left hψ; have h₂' := and_subformula_right hψ; aesop;
  · grind +suggestions;
  · rename_i ψ ih;
    constructor <;> intro h;
    · intro q hq;
      have hq_out : forces F v q.out ψ := by
        apply hq ψ hψ;
        have hq_out : subfmlEquiv F v φ x (Quotient.mk (subfmlSetoid F v φ) x).out :=
          mk_out_equiv F v φ x;
        exact hq_out _ hψ |>.1 h;
      convert ih _ _ |>.1 hq_out using 1;
      · exact Eq.symm ( Quotient.out_eq' q );
      · exact box_subformula_imp_subformula hψ;
    · contrapose! h;
      obtain ⟨y, hy⟩ : ∃ y, F.rel x y ∧ ¬forces F v y ψ := by
        exact Set.not_subset.mp h;
      have h_rel : (largestFiltrationFrame F v φ).rel ⟦x⟧ ⟦y⟧ := by
        apply smallestFilt_le_largestFilt;
        exact ⟨ x, y, subfmlEquiv_refl _, subfmlEquiv_refl _, hy.1 ⟩;
      have h_not_forces : ¬forces (largestFiltrationFrame F v φ) (filtrationVal F v φ) ⟦y⟧ ψ := by
        exact fun h => hy.2 <| ih y ( by
          exact box_subformula_imp_subformula hψ ) |>.2 h;
      exact fun h => h_not_forces <| h _ h_rel

/-!
## § 6. Finiteness and Cardinality Bound
-/

/-- The largest filtration is finite (same states as the smallest filtration). -/
noncomputable instance largestFiltration_finite (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Finite (largestFiltrationFrame F v φ).states :=
  filtration_finite F v φ

/-- The largest filtration has the same cardinality bound as the smallest:
    at most 2^|Sub(φ)| equivalence classes. -/
lemma largestFiltrationFrame_card_le (F : Frame) (v : Nat → F.states → Prop) (φ : Form) :
    @Fintype.card (largestFiltrationFrame F v φ).states (Fintype.ofFinite _) ≤
      2 ^ (subformulas φ).length :=
  filtrationFrame_card_le F v φ

end Modal