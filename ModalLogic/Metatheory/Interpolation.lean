/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen


# Craig Interpolation for Modal Logic K

This file proves the **Craig Interpolation Property (CIP)** for modal logic K:

> If `∅ ⊢K (φ ⊃ ψ)`, then there exists a formula `θ` (the *interpolant*) such that:
> 1. `∅ ⊢K (φ ⊃ θ)`
> 2. `∅ ⊢K (θ ⊃ ψ)`
> 3. `vars θ ⊆ vars φ ∩ vars ψ`

## Proof Strategy

The proof follows the standard model-theoretic argument via the canonical model:

1. Given `⊢K (φ ⊃ ψ)`, define V = vars φ ∩ vars ψ (common variables).
2. Let Σ = {χ | vars χ ⊆ V ∧ ⊢K (φ ⊃ χ)} be the V-consequences of φ.
3. Show Σ ∪ {∼ψ} is inconsistent by contradiction:
   - If consistent, extend to maximal w₂; build w₁ with φ ∈ w₁ agreeing with w₂ on V.
   - The V-agreement relation Z is a V-bisimulation on the canonical model.
   - A product model construction yields a single world satisfying φ ∧ ¬ψ,
     contradicting ⊨_K φ → ψ.
4. From inconsistency, extract a finite interpolant θ = fin_conj of V-consequences.

## References

- Blackburn, de Rijke, Venema. *Modal Logic*. Cambridge University Press, 2001. Chapter 6.
- Chellas. *Modal Logic: An Introduction*. Cambridge University Press, 1980. Chapter 6.
-/

import ModalLogic.Metatheory.Overview

open Classical
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

/-!
## § 1. Variable Irrelevance

The truth of a formula at a world depends only on the values of its
propositional variables.
-/

/--
**Variable irrelevance for forcing**: If two valuations agree on all variables
appearing in formula φ, then φ has the same truth value at any world.
-/
theorem forces_vars_agree {f : Frame.{0}} {v₁ v₂ : ℕ → f.states → Prop}
    (φ : Form) (hagree : ∀ n ∈ vars φ, ∀ w : f.states, v₁ n w ↔ v₂ n w) :
    ∀ w : f.states, forces f v₁ w φ ↔ forces f v₂ w φ := by
  induction' φ using Form.recOn with _ _ _ _ _ ih_1 ih_2
  · aesop
  · exact hagree _ (by tauto)
  · simp_all +decide [vars]
  · simp_all +decide [vars]; unfold forces; aesop
  · unfold vars at hagree; aesop

/-!
## § 2. V-Bisimulation and Product Model
-/

/--
**Product frame**: Given two frames and a relation Z ⊆ W₁ × W₂,
form a frame on Z with the product accessibility relation.
-/
def productFrame (F₁ F₂ : Frame.{0})
    (Z : F₁.states → F₂.states → Prop) : Frame.{0} where
  states := { p : F₁.states × F₂.states // Z p.1 p.2 }
  rel := fun ⟨⟨u₁, u₂⟩, _⟩ ⟨⟨v₁, v₂⟩, _⟩ => F₁.rel u₁ v₁ ∧ F₂.rel u₂ v₂

/--
**Product valuation**: Variables in S get values from the first component,
other variables get values from the second component.
-/
def productVal (F₁ F₂ : Frame.{0}) (Z : F₁.states → F₂.states → Prop)
    (v₁ : ℕ → F₁.states → Prop) (v₂ : ℕ → F₂.states → Prop)
    (S : Finset ℕ) : ℕ → (productFrame F₁ F₂ Z).states → Prop :=
  fun n ⟨⟨w₁, w₂⟩, _⟩ => if n ∈ S then v₁ n w₁ else v₂ n w₂

/--
A **V-bisimulation** between two Kripke models ensures agreement
on all formulas whose variables lie in V.
-/
structure VBisimulation (F₁ F₂ : Frame.{0}) (v₁ : ℕ → F₁.states → Prop)
    (v₂ : ℕ → F₂.states → Prop) (V : Finset ℕ)
    (Z : F₁.states → F₂.states → Prop) : Prop where
  atoms : ∀ w₁ w₂, Z w₁ w₂ → ∀ n ∈ V, (v₁ n w₁ ↔ v₂ n w₂)
  zig : ∀ w₁ w₂, Z w₁ w₂ → ∀ v₁', F₁.rel w₁ v₁' →
    ∃ v₂', F₂.rel w₂ v₂' ∧ Z v₁' v₂'
  zag : ∀ w₁ w₂, Z w₁ w₂ → ∀ v₂', F₂.rel w₂ v₂' →
    ∃ v₁', F₁.rel w₁ v₁' ∧ Z v₁' v₂'

/-!
## § 3. Product Model Preservation Lemmas
-/

/-
**Product preserves left formulas (zig only)**: For formulas with vars ⊆ S,
the product model agrees with the first component model. Only requires
the zig property (not full V-bisimulation atoms).
-/
theorem product_preserves_left_zig {F₁ F₂ : Frame.{0}}
    {v₁ : ℕ → F₁.states → Prop} {v₂ : ℕ → F₂.states → Prop}
    {Z : F₁.states → F₂.states → Prop} {S : Finset ℕ}
    (hzig : ∀ w₁ w₂, Z w₁ w₂ → ∀ u₁, F₁.rel w₁ u₁ →
      ∃ u₂, F₂.rel w₂ u₂ ∧ Z u₁ u₂)
    (θ : Form) (hθ : vars θ ⊆ S)
    (w₁ : F₁.states) (w₂ : F₂.states) (hw : Z w₁ w₂) :
    forces (productFrame F₁ F₂ Z) (productVal F₁ F₂ Z v₁ v₂ S)
      ⟨(w₁, w₂), hw⟩ θ ↔ forces F₁ v₁ w₁ θ := by
  induction' θ with θ₁ θ₂ ih₁ ih₂ generalizing w₁ w₂ hw;
  · exact Eq.to_iff rfl;
  · simp +decide [ productVal ];
    exact fun h => False.elim <| h <| hθ <| by tauto;
  · unfold vars at hθ; simp_all +decide [ Finset.subset_iff ] ;
  · unfold vars at hθ; simp_all +decide [ Finset.subset_iff, forces ] ;
  · constructor <;> intro h <;> simp_all +decide [ Finset.subset_iff ];
    · intro u hu
      obtain ⟨u₂, hu₂, huZ⟩ := hzig w₁ w₂ hw u hu
      have := h ⟨(u, u₂), huZ⟩ (by
      exact ⟨ hu, hu₂ ⟩)
      generalize_proofs at *;
      rename_i φ ih; specialize ih ( fun x hx => hθ <| by
        exact Finset.mem_def.mpr hx ) u u₂ huZ; aesop;
    · rintro ⟨ ⟨ u₁, u₂ ⟩, hu ⟩ hu';
      rename_i φ ih;
      convert ih ( fun x hx => hθ <| by
        exact Finset.mem_def.mpr hx ) u₁ u₂ hu |>.2 ( h u₁ hu'.1 ) using 1

/-
**Product preserves right formulas (with V-atoms)**:
For formulas whose variables in S are all in V (the agreement set),
the product model agrees with the second component model.
-/
theorem product_preserves_right_V {F₁ F₂ : Frame.{0}}
    {v₁ : ℕ → F₁.states → Prop} {v₂ : ℕ → F₂.states → Prop}
    {Z : F₁.states → F₂.states → Prop} {S V : Finset ℕ}
    (hatoms : ∀ w₁ w₂, Z w₁ w₂ → ∀ n ∈ V, (v₁ n w₁ ↔ v₂ n w₂))
    (hzag : ∀ w₁ w₂, Z w₁ w₂ → ∀ u₂, F₂.rel w₂ u₂ →
      ∃ u₁, F₁.rel w₁ u₁ ∧ Z u₁ u₂)
    (θ : Form) (hθV : ∀ n ∈ vars θ, n ∈ S → n ∈ V)
    (w₁ : F₁.states) (w₂ : F₂.states) (hw : Z w₁ w₂) :
    forces (productFrame F₁ F₂ Z) (productVal F₁ F₂ Z v₁ v₂ S)
      ⟨(w₁, w₂), hw⟩ θ ↔ forces F₂ v₂ w₂ θ := by
  induction' θ using Form.recOn with θ hθ generalizing w₁ w₂; aesop;
  · by_cases hθS : θ ∈ S <;> simp_all +decide [ productVal ];
    exact hatoms _ _ hw _ ( hθV _ ( by tauto ) hθS );
  · simp_all +decide [ vars ];
  · rename_i φ ψ hφ hψ;
    simp +decide [ forces ];
    rw [ hφ ( fun n hn hn' => hθV n ( by exact Finset.mem_union_left _ hn ) hn' ), hψ ( fun n hn hn' => hθV n ( by exact Finset.mem_union_right _ hn ) hn' ) ];
  · rename_i φ ih;
    constructor <;> intro h u hu;
    · obtain ⟨ u₁, hu₁, hu₂ ⟩ := hzag w₁ w₂ hw u hu;
      exact ih ( fun n hn hn' => hθV n ( by
        exact Finset.mem_def.mpr hn ) hn' ) u₁ u hu₂ |>.1 ( h ⟨ ( u₁, u ), hu₂ ⟩ ⟨ hu₁, hu ⟩ );
    · exact ih ( fun n hn hn' => hθV n ( by
        exact Finset.mem_def.mpr hn ) hn' ) _ _ u.2 |>.2 ( h _ hu.2 )

/-!
## § 4. Auxiliary Lemmas for fin_conj
-/

/-
If all elements of L have vars ⊆ V, then vars (fin_conj L) ⊆ V.
-/
lemma vars_fin_conj_of_all (L : List Form) (V : Finset ℕ)
    (h : ∀ φ ∈ L, vars φ ⊆ V) : vars (fin_conj L) ⊆ V := by
  induction' L with φ L ih;
  · exact Finset.inter_eq_left.mp rfl;
  · intro x hx; unfold vars at hx; aesop;

/-
If all elements of L are in a maximal set, then fin_conj L is also in it.
-/
lemma fin_conj_mem_maximal {AX : Ctx} (w : World AX) (L : List Form)
    (h : ∀ φ ∈ L, World.mem φ w) : World.mem (fin_conj L) w := by
  apply World.proves;
  convert h using 1;
  exact identity_simp

/-
If ⊢K (φ ⊃ χᵢ) for all i, then ⊢K (φ ⊃ fin_conj [χ₁,...,χₙ]).
-/
lemma phi_implies_fin_conj {AX : Ctx} (φ : Form) (L : List Form)
    (h : ∀ χ ∈ L, ProofK AX (φ ⊃ χ)) : ProofK AX (φ ⊃ fin_conj L) := by
  induction' L with χ L ih generalizing φ;
  · grind +suggestions;
  · have := ih φ ( by aesop );
    have h_fin_conj : AX ⊢K φ ⟹ (χ & fin_conj L) := by
      have h1 : AX ⊢K φ ⟹ χ := by
        aesop
      have h2 : AX ⊢K φ ⟹ fin_conj L := by
        assumption
      have h3 : AX ⊢K (χ ⊃ (fin_conj L ⊃ (χ & fin_conj L))) := by
        exact pl4;
      have h4 : AX ⊢K φ ⟹ (fin_conj L ⊃ (χ & fin_conj L)) := by
        exact impl_chain2 h1 h3;
      have h5 : AX ⊢K (φ ⊃ (fin_conj L ⊃ (χ & fin_conj L))) → AX ⊢K (φ ⊃ fin_conj L) → AX ⊢K (φ ⊃ (χ & fin_conj L)) := by
        intros h4 h5;
        have h6 : AX ⊢K (φ ⊃ (fin_conj L ⊃ (χ & fin_conj L))) → AX ⊢K (φ ⊃ fin_conj L) → AX ⊢K (φ ⊃ (χ & fin_conj L)) := by
          intros h4 h5
          have h6 : AX ⊢K ((φ ⊃ (fin_conj L ⊃ (χ & fin_conj L))) ⊃ ((φ ⊃ fin_conj L) ⊃ (φ ⊃ (χ & fin_conj L)))) := by
            exact pl2
          grind +suggestions;
        exact h6 h4 h5;
      exact h5 h4 h2;
    exact h_fin_conj

/-
Contrapositive rearrangement: from ⊢K (fin_conj L' ⊃ (φ ⊃ ⊥)),
    derive ⊢K (φ ⊃ ∼(fin_conj L')).
-/
lemma conj_imp_neg_rearrange {AX : Ctx} {L' : List Form} {φ : Form}
    (h : ProofK AX (fin_conj L' ⊃ (φ ⊃ ⊥ₘ))) :
    ProofK AX (φ ⊃ ∼(fin_conj L')) := by
  -- From h : ⊢K (fin_conj L' ⊃ (φ ⊃ ⊥ₘ)), by swapping the two antecedents using double_imp or imp_switch, we get ⊢K (φ ⊃ (fin_conj L' ⊃ ⊥ₘ)).
  have hswap : AX ⊢K (φ ⊃ (fin_conj L' ⊃ ⊥ₘ)) := by
    exact imp_switch h;
  convert hswap using 1

/-!
## § 5. Canonical V-Bisimulation
-/

/--
The V-agreement relation on the canonical model: two worlds agree
on all formulas whose variables lie in V.
-/
def canonicalVAgree (V : Finset ℕ) (w₁ w₂ : World (∅ : Ctx)) : Prop :=
  ∀ χ : Form, vars χ ⊆ V → (World.mem χ w₁ ↔ World.mem χ w₂)

/-
**Iterated five_helper**: Given L ⊆ Γ_keep ∪ Γ_peel and ⊢K (fin_conj L ⊃ b),
produce L_keep ⊆ Γ_keep and L_peel ⊆ Γ_peel with
⊢K (fin_conj L_keep ⊃ (fin_conj L_peel ⊃ b)).
-/
lemma iterated_five_helper {AX : Ctx} (Gamma_keep Gamma_peel : Ctx)
    (L : List Form) (b : Form)
    (hL : ∀ ψ ∈ L, ψ ∈ Gamma_keep ∨ ψ ∈ Gamma_peel)
    (hprf : ProofK AX (fin_conj L ⊃ b)) :
    ∃ L_keep L_peel : List Form,
      (∀ ψ ∈ L_keep, ψ ∈ Gamma_keep) ∧
      (∀ ψ ∈ L_peel, ψ ∈ Gamma_peel) ∧
      ProofK AX (fin_conj L_keep ⊃ (fin_conj L_peel ⊃ b)) := by
  -- Let's choose any $l \in L$.
  induction' L with l L ih generalizing b <;> simp_all +decide [ fin_conj ];
  · use [], by simp, [], by simp;
    exact imp_if_imp_imp hprf;
  · -- By the and_right_imp lemma, we can split the implication into two parts.
    have h_split : AX ⊢K fin_conj L ⟹ (l ⊃ b) := by
      exact imp_conj_imp_imp.mp hprf;
    obtain ⟨ L_keep, hL_keep, L_peel, hL_peel, h ⟩ := ih _ h_split;
    cases' hL.1 with hl hl;
    · refine' ⟨ l :: L_keep, _, L_peel, _, _ ⟩ <;> simp_all +decide [ fin_conj ];
      have h_split : AX ⊢K fin_conj L_keep ⟹ (l ⊃ (fin_conj L_peel ⟹ b)) := by
        exact imp_shift.mp h;
      exact and_right_imp.mpr h_split;
    · use L_keep, hL_keep, l :: L_peel;
      simp_all +decide [ fin_conj_cons ];
      grind +suggestions

/-
**Zig consistency**: The set {χ | □χ ∈ w₂} ∪ {χ | vars χ ⊆ V ∧ χ ∈ w₁'}
is consistent, given V-agreement between w₁, w₂ and canonical accessibility
from w₁ to w₁'.
-/
lemma canonical_zig_consistent (V : Finset ℕ)
    (w₁ w₂ : World (∅ : Ctx))
    (hZ : canonicalVAgree V w₁ w₂)
    (w₁' : World (∅ : Ctx))
    (hR : (canonicalFrame ∅).rel w₁ w₁') :
    ax_consist ∅
      ({χ | World.mem (Form.box χ) w₂} ∪
       {χ | vars χ ⊆ V ∧ World.mem χ w₁'}) := by
  intro L hL hprf
  by_contra h_contra
  obtain ⟨L_keep, L_peel, hL_keep, hL_peel, hprf⟩ := iterated_five_helper {χ | World.mem (□ χ) w₂} {χ | vars χ ⊆ V ∧ World.mem χ w₁'} L ⊥ₘ hL hprf;
  -- By World.derives with fin_conj_boxn and then box_mono result: □(∼(fin_conj L_peel)) ∈ w₂.
  have h_box_neg_fin_conj : World.mem (□ (∼ (fin_conj L_peel))) w₂ := by
    have h_box_neg_fin_conj : World.mem (□ (fin_conj L_keep)) w₂ := by
      apply World.proves;
      any_goals exact L_keep.map fun x => □x;
      · grind;
      · exact fin_conj_boxn;
    apply World.derives w₂ h_box_neg_fin_conj;
    exact box_mono hprf;
  -- By hZ (canonicalVAgree V w₁ w₂): □(∼(fin_conj L_peel)) ∈ w₁ (using the backward direction of the iff, since it's in w₂).
  have h_box_neg_fin_conj_w1 : World.mem (□ (∼ (fin_conj L_peel))) w₁ := by
    have h_vars_subset : vars (fin_conj L_peel) ⊆ V := by
      apply_rules [ vars_fin_conj_of_all ];
      exact fun ψ hψ => hL_peel ψ hψ |>.1;
    have h_vars_subset : vars (fin_conj L_peel ⟹ ⊥ₘ) ⊆ V := by
      exact Finset.union_subset h_vars_subset ( Finset.empty_subset _ );
    exact hZ _ ( by simpa using h_vars_subset ) |>.2 h_box_neg_fin_conj;
  -- By hR (canonical accessibility w₁ → w₁'): ∼(fin_conj L_peel) ∈ w₁'.
  have h_neg_fin_conj_w1' : World.mem (∼ (fin_conj L_peel)) w₁' := by
    exact hR _ h_box_neg_fin_conj_w1;
  exact World.no_contradiction w₁' _ ⟨ fin_conj_mem_maximal w₁' L_peel fun ψ hψ => hL_peel ψ hψ |>.2, h_neg_fin_conj_w1' ⟩

/-
**Zig property for canonical V-agreement**.
-/
theorem canonical_V_zig (V : Finset ℕ)
    (w₁ w₂ : World (∅ : Ctx))
    (hZ : canonicalVAgree V w₁ w₂)
    (w₁' : World (∅ : Ctx))
    (hR : (canonicalFrame ∅).rel w₁ w₁') :
    ∃ w₂' : World (∅ : Ctx),
      (canonicalFrame ∅).rel w₂ w₂' ∧ canonicalVAgree V w₁' w₂' := by
  -- By canonical_zig_consistent, {χ | World.mem (Form.box χ) w₂} ∪ {χ | vars χ ⊆ V ∧ World.mem χ w₁'} is `AX`-consistent.
  have h_consistent : ax_consist ∅ ({χ | World.mem (Form.box χ) w₂} ∪ {χ | vars χ ⊆ V ∧ World.mem χ w₁'}) := by
    exact canonical_zig_consistent V w₁ w₂ hZ w₁' hR;
  obtain ⟨w₂', hw₂'⟩ : ∃ w₂' : World ∅,ax_consist ∅ w₂'.val ∧ ({χ | World.mem (Form.box χ) w₂} ∪ {χ | vars χ ⊆ V ∧ World.mem χ w₁'}) ⊆ w₂'.val := by
    obtain ⟨w₂', hw₂'⟩ : ∃ w₂' : World ∅,ax_consist ∅ w₂'.val ∧ ({χ | World.mem (Form.box χ) w₂} ∪ {χ | vars χ ⊆ V ∧ World.mem χ w₁'}) ⊆ w₂'.val := by
      have := lindenbaum ∅ ({χ | World.mem (Form.box χ) w₂} ∪ {χ | vars χ ⊆ V ∧ World.mem χ w₁'}) h_consistent
      exact ⟨ ⟨ this.choose, this.choose_spec.1 ⟩, this.choose_spec.1.1, this.choose_spec.2 ⟩;
    use w₂';
  refine' ⟨ w₂', _, _ ⟩;
  · exact fun φ hφ => hw₂'.2 ( Set.mem_union_left _ hφ );
  · intro χ hχ; by_cases h : World.mem χ w₁' <;> simp_all +decide [ Set.subset_def ] ;
    · exact hw₂'.2 χ ( Or.inr ⟨ hχ, h ⟩ );
    · have := World.no_contradiction w₁' χ; simp_all +decide [ World.mem ] ;
      grind +suggestions

/-
**Zag property for canonical V-agreement**.
-/
theorem canonical_V_zag (V : Finset ℕ)
    (w₁ w₂ : World (∅ : Ctx))
    (hZ : canonicalVAgree V w₁ w₂)
    (w₂' : World (∅ : Ctx))
    (hR : (canonicalFrame ∅).rel w₂ w₂') :
    ∃ w₁' : World (∅ : Ctx),
      (canonicalFrame ∅).rel w₁ w₁' ∧ canonicalVAgree V w₁' w₂' := by
  convert canonical_V_zig V w₂ w₁ ( fun χ hχ => ?_ ) w₂' hR using 1;
  · grind +locals;
  · exact hZ χ hχ |> Iff.symm

/-!
## § 6. Craig Interpolation — Syntactic Version
-/

/-
**Syntactic Craig Interpolation for K**.
-/
theorem syntactic_craig_interpolation (φ ψ : Form) (h : ∅ ⊢K (φ ⊃ ψ)) :
    ∃ θ : Form, (∅ ⊢K (φ ⊃ θ)) ∧ (∅ ⊢K (θ ⊃ ψ)) ∧
      vars θ ⊆ vars φ ∩ vars ψ := by
  convert Classical.byContradiction _;
  intro h_contra
  set V := vars φ ∩ vars ψ
  set SigmaSet := {χ : Form | vars χ ⊆ V ∧ ProofK ∅ (φ ⊃ χ)} ∪ {∼ψ};
  -- Assume ax_consist ∅ SigmaSet.
  by_cases h_consistent : ax_consist ∅ SigmaSet;
  · obtain ⟨w₂, hw₂⟩ : ∃ w₂ : World (∅ : Ctx), ∼ψ ∈ w₂.val ∧ ∀ χ : Form, vars χ ⊆ V → ProofK ∅ (φ ⊃ χ) → χ ∈ w₂.val := by
      have := lindenbaum ∅ SigmaSet h_consistent;
      obtain ⟨ Γ', hΓ₁, hΓ₂ ⟩ := this; use ⟨ Γ', hΓ₁ ⟩ ; aesop;
    -- Show Delta is consistent: Take L with elements from Delta and ⊢K (fin_conj L ⊃ ⊥ₘ).
    have h_delta_consistent : ax_consist ∅ ({φ} ∪ {χ : Form | vars χ ⊆ V ∧ χ ∈ w₂.val}) := by
      intro L hL hL';
      -- Use five_helper to separate φ: get L' ⊆ {V-theory of w₂} with ⊢K (fin_conj L' ⊃ (φ ⊃ ⊥ₘ)).
      obtain ⟨L', hL'_subset, hL'_proof⟩ : ∃ L' : List Form, (∀ ψ ∈ L', ψ ∈ {χ : Form | vars χ ⊆ V ∧ χ ∈ w₂.val}) ∧ ProofK ∅ (fin_conj L' ⊃ (φ ⊃ ⊥ₘ)) := by
        apply five_helper;
        any_goals assumption;
        grind;
      -- So ∼(fin_conj L') ∈ SigmaSet ⊆ w₂.
      have h_neg_fin_conj_L'_in_w2 : ∼(fin_conj L') ∈ w₂.val := by
        apply hw₂.right;
        · have h_vars_fin_conj : vars (fin_conj L') ⊆ V := by
            apply vars_fin_conj_of_all;
            exact fun ψ hψ => hL'_subset ψ hψ |>.1;
          convert h_vars_fin_conj using 1;
          exact vars_neg (fin_conj L');
        · exact conj_imp_neg_rearrange hL'_proof;
      -- But all elements of L' are in w₂, so fin_conj L' ∈ w₂ (fin_conj_mem_maximal).
      have h_fin_conj_L'_in_w2 : fin_conj L' ∈ w₂.val := by
        exact fin_conj_mem_maximal w₂ L' fun ψ hψ => hL'_subset ψ hψ |>.2;
      exact w₂.no_contradiction _ ⟨ h_fin_conj_L'_in_w2, h_neg_fin_conj_L'_in_w2 ⟩;
    -- Extend Delta to maximal w₁. φ ∈ w₁. w₁ and w₂ agree on V-formulas (canonicalVAgree V w₁ w₂).
    obtain ⟨w₁, hw₁⟩ : ∃ w₁ : World (∅ : Ctx), φ ∈ w₁.val ∧ ∀ χ : Form, vars χ ⊆ V → (χ ∈ w₁.val ↔ χ ∈ w₂.val) := by
      obtain ⟨w₁, hw₁⟩ : ∃ w₁ : World (∅ : Ctx), {φ} ∪ {χ : Form | vars χ ⊆ V ∧ χ ∈ w₂.val} ⊆ w₁.val := by
        have := lindenbaum ∅ _ h_delta_consistent;
        exact ⟨ ⟨ this.choose, this.choose_spec.1 ⟩, this.choose_spec.2 ⟩;
      refine' ⟨ w₁, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
      grind +suggestions;
    -- By truthLemma: forces canonical w₁ φ and ¬forces canonical w₂ ψ.
    have h_forces_w1 : forces (canonicalFrame ∅) canonicalVal w₁ φ := by
      exact truthLemma ∅ w₁ φ |>.2 hw₁.1
    have h_forces_w2 : ¬forces (canonicalFrame ∅) canonicalVal w₂ ψ := by
      rw [ truthLemma ];
      exact fun h => World.no_contradiction w₂ ψ ⟨ h, hw₂.1 ⟩;
    -- Canonical V-bisimulation Z = canonicalVAgree V has atoms, zig, zag properties.
    have h_bisimulation : VBisimulation (canonicalFrame ∅) (canonicalFrame ∅) canonicalVal canonicalVal V (fun w₁ w₂ => ∀ χ : Form, vars χ ⊆ V → (χ ∈ w₁.val ↔ χ ∈ w₂.val)) := by
      constructor;
      · intro w₁ w₂ hZ n hn; specialize hZ ( Form.var n ) ; simp_all +decide [ canonicalVal ] ;
        exact hZ ( by simpa [ vars ] using hn );
      · intros w₁ w₂ hZ v₁' hv₁';
        apply canonical_V_zig V w₁ w₂ hZ v₁' hv₁';
      · intros w₁ w₂ hZ v₂' hv₂'
        obtain ⟨v₁', hv₁', hv₁'Z⟩ := canonical_V_zag V w₁ w₂ hZ v₂' hv₂'
        use v₁';
        exact ⟨ hv₁', hv₁'Z ⟩;
    -- Build product model with S = vars φ. By product_preserves_left_zig: product ⊨ φ at (w₁,w₂).
    have h_product_forces_w1 : forces (productFrame (canonicalFrame ∅) (canonicalFrame ∅) (fun w₁ w₂ => ∀ χ : Form, vars χ ⊆ V → (χ ∈ w₁.val ↔ χ ∈ w₂.val))) (productVal (canonicalFrame ∅) (canonicalFrame ∅) (fun w₁ w₂ => ∀ χ : Form, vars χ ⊆ V → (χ ∈ w₁.val ↔ χ ∈ w₂.val)) canonicalVal canonicalVal (vars φ)) ⟨(w₁, w₂), hw₁.2⟩ φ := by
      apply (product_preserves_left_zig h_bisimulation.zig φ (by
      exact Finset.Subset.refl _) w₁ w₂ hw₁.2).mpr h_forces_w1;
    -- By product_preserves_right_V: product ⊨ ψ ↔ canonical ⊨ ψ at w₂ (since vars ψ ∩ S = vars ψ ∩ vars φ = V).
    have h_product_forces_w2 : ¬forces (productFrame (canonicalFrame ∅) (canonicalFrame ∅) (fun w₁ w₂ => ∀ χ : Form, vars χ ⊆ V → (χ ∈ w₁.val ↔ χ ∈ w₂.val))) (productVal (canonicalFrame ∅) (canonicalFrame ∅) (fun w₁ w₂ => ∀ χ : Form, vars χ ⊆ V → (χ ∈ w₁.val ↔ χ ∈ w₂.val)) canonicalVal canonicalVal (vars φ)) ⟨(w₁, w₂), hw₁.2⟩ ψ := by
      rw [ product_preserves_right_V ];
      exact h_forces_w2;
      exact fun w₁ w₂ a n a_1 => h_bisimulation.atoms w₁ w₂ a n a_1;
      · exact fun w₁ w₂ h u₂ hu₂ => by obtain ⟨ u₁, hu₁, hu₁' ⟩ := h_bisimulation.zag w₁ w₂ h u₂ hu₂; exact ⟨ u₁, hu₁, hu₁' ⟩ ;
      · exact fun n hn₁ hn₂ => Finset.mem_inter.mpr ⟨ hn₂, hn₁ ⟩;
    apply h_product_forces_w2;
    apply (soundness ∅ (φ ⊃ ψ) h);
    · grind;
    · exact h_product_forces_w1;
  · -- Use five_helper to separate ∼ψ from L: get L' ⊆ {V-consequences of φ} with ⊢K (fin_conj L' ⊃ (∼ψ ⊃ ⊥ₘ)).
    obtain ⟨L', hL'⟩ : ∃ L' : List Form, (∀ ψ ∈ L', ψ ∈ {χ : Form | vars χ ⊆ V ∧ ProofK ∅ (φ ⊃ χ)}) ∧ ProofK ∅ (fin_conj L' ⊃ (∼ψ ⊃ ⊥ₘ)) := by
      exact five ∅ {χ | vars χ ⊆ V ∧ ∅ ⊢K φ ⟹ χ} (¬ₘψ) h_consistent;
    -- So ⊢K (fin_conj L' ⊃ ψ) (by cut with dne: ∼ψ ⊃ ⊥ₘ is ∼∼ψ, and dne gives ∼∼ψ ⊃ ψ, so fin_conj L' ⊃ ∼∼ψ by the proof, then cut with dne).
    have h_fin_conj_L'_implies_psi : ProofK ∅ (fin_conj L' ⊃ ψ) := by
      apply cut hL'.right;
      apply dne;
    refine' h_contra ⟨ fin_conj L', _, _, _ ⟩ <;> simp_all +decide ;
    · apply phi_implies_fin_conj;
      exact fun χ hχ => hL'.1 χ hχ |>.2;
    · exact vars_fin_conj_of_all L' V fun χ hχ => hL'.1 χ hχ |>.1

/-!
## § 7. Semantic Craig Interpolation
-/

/--
**Semantic Craig Interpolation**: If φ → ψ is valid in all K-frames,
then there exists an interpolant θ.
-/
theorem semantic_craig_interpolation (φ ψ : Form)
    (hvalid : ∀ (F : Frame.{0}) (v : ℕ → F.states → Prop) (w : F.states),
      forces F v w φ → forces F v w ψ) :
    ∃ θ : Form, vars θ ⊆ vars φ ∩ vars ψ ∧
      (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop) (w : F.states),
        forces F v w φ → forces F v w θ) ∧
      (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop) (w : F.states),
        forces F v w θ → forces F v w ψ) := by
  -- By completeness, ⊢K (φ ⊃ ψ)
  have h_syn : ∅ ⊢K (φ ⊃ ψ) := by
    apply completeness_K; intro F v w; exact hvalid F v w
  -- By syntactic interpolation
  obtain ⟨θ, h1, h2, hvars⟩ := syntactic_craig_interpolation φ ψ h_syn
  -- By soundness, convert to semantic
  refine ⟨θ, hvars, ?_, ?_⟩
  · intro F v w hφ
    exact (soundness ∅ (φ ⊃ θ) h1) F v (fun _ _ h => False.elim h) w hφ
  · intro F v w hθ
    exact (soundness ∅ (θ ⊃ ψ) h2) F v (fun _ _ h => False.elim h) w hθ

/-!
## § 8. Craig Interpolation Theorem
-/

/--
**Craig Interpolation for Modal Logic K**.
-/
theorem craig_interpolation (φ ψ : Form) (h : ∅ ⊢K (φ ⊃ ψ)) :
    ∃ θ : Form, (∅ ⊢K (φ ⊃ θ)) ∧ (∅ ⊢K (θ ⊃ ψ)) ∧ vars θ ⊆ vars φ ∩ vars ψ :=
  syntactic_craig_interpolation φ ψ h

/-!
## § 9. Beth Definability (Corollary)
-/

/--
**Implicit definability**: A variable p is implicitly defined by φ if
any two models agreeing on all variables except p that both satisfy φ
must also agree on p.
-/
def ImplicitlyDefined (φ : Form) (p : ℕ) : Prop :=
  ∀ (F : Frame.{0}) (v₁ v₂ : ℕ → F.states → Prop) (w : F.states),
    (∀ n, n ≠ p → ∀ u : F.states, v₁ n u ↔ v₂ n u) →
    forces F v₁ w φ → forces F v₂ w φ →
    (v₁ p w ↔ v₂ p w)

/--
**Explicit definability**: A variable p is explicitly defined by φ if
there exists a formula θ not containing p such that φ ⊢K (p ↔ θ).
-/
def ExplicitlyDefined (φ : Form) (p : ℕ) : Prop :=
  ∃ θ : Form, p ∉ vars θ ∧ ∅ ⊢K (φ ⊃ (Form.var p ⇔ θ))

/-
Semantic substitution lemma for variable-for-variable substitution:
    Evaluating φ[p/q] under v is the same as evaluating φ under v[p ↦ v(q)].
-/
lemma forces_subst_var {f : Frame.{0}} {v : ℕ → f.states → Prop}
    (φ : Form) (p q : ℕ) (w : f.states) :
    forces f v w (subst φ p (Form.var q)) ↔
    forces f (fun n => if n = p then v q else v n) w φ := by
  convert forces_vars_agree _ _ _ using 1;
  rotate_left;
  exact fun n w => if n = p then v q w else v n w;
  · intro n hn w; split_ifs <;> simp_all +decide ;
    contrapose! hn;
    induction' φ with φ ψ hφ hψ generalizing p q <;> simp_all +decide [ subst ];
    · exact Finset.disjoint_singleton_left.mp fun ⦃x⦄ a a_1 => a_1;
    · split_ifs <;> simp_all +decide [ vars ];
      · grind;
      · tauto;
    · unfold vars; aesop;
    · unfold vars; aesop;
    · exact fun h => by have := ‹∀ ( p_1 q : ℕ ), p = p_1 → v p_1 w ∧ ¬v q w ∨ ¬v p_1 w ∧ v q w → p_1 ∉ vars ( subst _ p_1 p[q] ) › p q rfl hn; exact this ( by simpa [ vars ] using h ) ;
  · induction' φ with φ ψ hφ hψ generalizing p q w <;> simp +decide [ *, subst ];
    · split_ifs <;> simp +decide [ *, forces ];
    · simp +decide [ *, forces ]

/-
Uniform substitution metatheorem: if ⊢K ψ then ⊢K ψ[n/Form.var m].
-/
lemma uniform_subst_var {AX : Ctx} {ψ : Form} (n m : ℕ)
    (h : ProofK AX ψ) (hAX : ∀ χ ∈ AX, subst χ n (Form.var m) = χ) :
    ProofK AX (subst ψ n (Form.var m)) := by
  -- By the induction hypothesis, we know that `subst ψ n (Form.var m)` is provable from `AX`.
  have h_ind : ∀ (ψ : Form), (AX ⊢K ψ) → (AX ⊢K (subst ψ n (Form.var m))) := by
    intro ψ hψ
    induction' hψ with ψ ih;
    all_goals simp_all +decide [ subst ];
    all_goals first
      | exact ProofK.pl1
      | exact ProofK.pl2
      | exact ProofK.pl3
      | exact ProofK.pl4
      | exact ProofK.pl5
      | exact ProofK.pl6
      | exact ProofK.kdist
      | exact ProofK.mp ‹_› ‹_›
      | exact ProofK.nec ‹_›
  exact h_ind ψ h

/-
vars of a variable-for-variable substitution.
-/
lemma vars_subst_var (φ : Form) (p q : ℕ) :
    vars (subst φ p (Form.var q)) ⊆ (vars φ \ {p}) ∪ {q} := by
  induction' φ with φ₁ φ₂ ih₁ ih₂ <;> simp +decide [ *, Finset.subset_iff ];
  · tauto;
  · -- By definition of substitution, we know that if x is in the variables of the substituted formula, then x must be in the variables of the original formula and not equal to p.
    simp [subst, vars];
    split_ifs <;> simp_all +decide [ vars ];
  · intro x hx; rw [ show subst ( φ₂ ⋏ ih₁ ) p p[q] = subst φ₂ p p[q] ⋏ subst ih₁ p p[q] by rfl ] at hx; simp_all +decide [ vars ] ;
    grind +ring;
  · intro x hx; have := Finset.mem_union.mp hx; simp_all +decide [ Finset.subset_iff ] ;
    cases this <;> simp_all +decide [ vars ];
    · grind;
    · grind;
  · rename_i φ ih;
    intro x hx; specialize ih; unfold subst at hx; simp_all +decide [ Finset.subset_iff ] ;
    exact ih hx

/-
If q ∉ vars φ and q ≠ p, then subst (subst φ p (var q)) q (var p) = φ.
-/
lemma subst_var_roundtrip (φ : Form) (p q : ℕ) (hq : q ∉ vars φ) (hpq : p ≠ q) :
    subst (subst φ p (Form.var q)) q (Form.var p) = φ := by
  have h_subst_oracle : ∀ (φ : Form), q ∉ vars φ → p ≠ q → subst (subst φ p (Form.var q)) q (Form.var p) = φ := by
    intro φ hq hpq;
    induction' φ with φ₁ φ₂ ih₁ ih₂;
    · rfl;
    · by_cases h : φ₁ = p <;> simp_all +decide [ subst ];
      exact fun h' => hq <| h'.symm ▸ by simp +decide [ vars ] ;
    · simp_all +decide [ Finset.mem_union, vars ];
      exact congr_arg₂ _ ih₂ ‹_›;
    · simp_all +decide [ vars ];
      exact congr_arg₂ ( · ⟹ · ) ‹_› ‹_›;
    · exact congr_arg _ ( by solve_by_elim );
  exact h_subst_oracle φ hq hpq

/-
Helper: choose a fresh variable not in a Finset and not equal to p.
-/
lemma exists_fresh (S : Finset ℕ) (p : ℕ) : ∃ q, q ∉ S ∧ q ≠ p := by
  exact Exists.imp ( by aesop ) ( Finset.exists_notMem ( S ∪ { p } ) )

/-
Helper: if n ∉ vars φ, then subst φ n ψ = φ.
-/
lemma subst_not_in_vars (φ : Form) (n : ℕ) (ψ : Form) (h : n ∉ vars φ) :
    subst φ n ψ = φ := by
  revert φ ψ n h;
  intros φ n ψ hn; induction' φ with φ₁ φ₂ h₁ h₂ generalizing n ψ; all_goals simp_all +decide [ vars ] ;
  · rfl;
  · exact if_neg ( by aesop );
  · exact congr_arg₂ _ ( h₂ n ψ hn.1 ) ( ‹∀ ( n : ℕ ) ( ψ : Form ), n ∉ vars h₁ → subst h₁ n ψ = h₁› n ψ hn.2 );
  · unfold subst; aesop;
  · (expose_names; exact Eq.subst (congrArg Form.box (φ_ih n ψ hn)) rfl)

/-
Helper: combine two implications into a biconditional under a common antecedent.
-/
lemma combine_impl_to_iff {AX : Ctx} {φ a b : Form}
    (h1 : ProofK AX (φ ⊃ (a ⊃ b))) (h2 : ProofK AX (φ ⊃ (b ⊃ a))) :
    ProofK AX (φ ⊃ (a ⇔ b)) := by
  -- From h1 and h2, we can derive ⊢K (φ ⊃ ((a ⊃ b) & (b ⊃ a))) using the properties of implication and conjunction.
  have h3 : AX ⊢K (φ ⟹ ((a ⟹ b) & (b ⟹ a))) := by
    apply ProofK.mp;
    apply ProofK.mp;
    apply ProofK.pl2;
    exact b ⟹ a;
    · apply ProofK.mp;
      apply ProofK.mp;
      apply ProofK.pl2;
      exact a ⟹ b;
      · apply ProofK.mp;
        exact pl1;
        exact pl4;
      · assumption;
    · assumption;
  exact h3

/-
**Beth Definability Theorem for K**: Implicit definability implies explicit
definability.
-/
theorem beth_definability (φ : Form) (p : ℕ) :
    ImplicitlyDefined φ p → ExplicitlyDefined φ p := by
  -- Step 1: Choose fresh q ∉ vars φ with q ≠ p (using exists_fresh (vars φ) p).
  intro h_implicit
  obtain ⟨q, hq⟩ : ∃ q, q ∉ vars φ ∧ q ≠ p := exists_fresh (vars φ) p;
  -- By step 4, we have ⊢K ((φ & Form.var p) ⊃ (φ' ⊃ Form.var q)).
  have h_step4 : ProofK ∅ ((φ & Form.var p) ⊃ (subst φ p (Form.var q) ⊃ Form.var q)) := by
    apply completeness_K;
    intro F v w hφp hφq;
    have := h_implicit F v ( fun n => if n = p then v q else v n ) w; simp_all +decide [ forces_subst_var ] ;
  -- By step 5, we have ∃ θ with ⊢K ((φ & Form.var p) ⊃ θ), ⊢K (θ ⊃ (φ' ⊃ Form.var q)), and vars θ ⊆ vars (φ & Form.var p) ∩ vars (φ' ⊃ Form.var q).
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ : ∃ θ : Form, (∅ ⊢K ((φ & Form.var p) ⊃ θ)) ∧ (∅ ⊢K (θ ⊃ (subst φ p (Form.var q) ⊃ Form.var q))) ∧ vars θ ⊆ vars (φ & Form.var p) ∩ vars (subst φ p (Form.var q) ⊃ Form.var q) := by
    exact craig_interpolation (φ ⋏ p[p]) (subst φ p p[q] ⟹ p[q]) h_step4;
  have hθ4 : p ∉ vars θ := by
    intro hp; specialize hθ3 hp; simp_all +decide [ vars ] ;
    have h_vars_subst : vars (subst φ p (Form.var q)) ⊆ (vars φ \ {p}) ∪ {q} := by
      exact vars_subst_var φ p q;
    grind
  have hθ5 : q ∉ vars θ := by
    intro hqθ; have := hθ3 hqθ; simp_all +decide [ vars ] ;
  have hθ6 : ∅ ⊢K (φ ⊃ (Form.var p ⊃ θ)) := by
    have hθ6 : ∅ ⊢K (Form.var p ⊃ (φ ⊃ θ)) := by
      exact and_right_imp.mp hθ1;
    exact imp_switch hθ6
  have hθ7 : ∅ ⊢K (φ ⊃ (θ ⊃ Form.var p)) := by
    have hθ7 : ∅ ⊢K (subst θ q (Form.var p) ⊃ (subst (subst φ p (Form.var q)) q (Form.var p) ⊃ subst (Form.var q) q (Form.var p))) := by
      apply uniform_subst_var q p hθ2; simp +decide ;
    have hθ8 : subst θ q (Form.var p) = θ := by
      exact subst_not_in_vars θ q p[p] hθ5
    have hθ9 : subst (subst φ p (Form.var q)) q (Form.var p) = φ := by
      apply subst_var_roundtrip; exact hq.left; exact hq.right.symm;
    have hθ10 : subst (Form.var q) q (Form.var p) = Form.var p := by
      exact if_pos rfl
    rw [hθ8, hθ9, hθ10] at hθ7
    exact (by
    exact imp_switch hθ7)
  use θ;
  exact ⟨ hθ4, combine_impl_to_iff hθ6 hθ7 ⟩

end
