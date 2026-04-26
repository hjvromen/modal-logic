import ModalLogic.Metatheory.Canonical

/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen
-/

/-!
# Completeness Theorems for KD and KB

This file proves the completeness theorems for modal logics KD and KB,
extending the existing completeness results for K, T, S4, and S5.

## KD Completeness

**KD** extends K with the D axiom: □φ → ◇φ (necessity implies possibility).
KD is sound and complete with respect to **serial frames** (every world has
at least one successor).

**Strategy**: Show the canonical frame for KD is serial. Given a maximally
KD-consistent set w, the D axiom ensures that for any world w, the set
{ψ | □ψ ∈ w} is consistent (otherwise □⊥ ∈ w, and by D, ◇⊥ ∈ w, contradiction).
This consistent set extends to a maximal set w', giving w R w'.

## KB Completeness

**KB** extends K with the B axiom: φ → □◇φ (truth implies necessary possibility).
KB is sound and complete with respect to **symmetric frames**.

**Strategy**: Show the canonical frame for KB is symmetric. If w₁ R w₂
(i.e., □ψ ∈ w₁ implies ψ ∈ w₂), we need w₂ R w₁. Suppose □χ ∈ w₂;
we need χ ∈ w₁. By B, χ → □◇χ, so if χ ∉ w₁, then ¬χ ∈ w₁, hence
□¬χ is accessible... The proof uses the B axiom to establish symmetry.
-/

open Classical
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

/-!
## Helper: D axiom gives diamond from box
-/

/--
**D axiom derivation helper**: In the context of KD axioms,
□ψ ⊃ ◇ψ is provable (it's an axiom).
-/
private lemma kd_box_to_dia {ψ : Form} :
    ProofK KDAxioms (□ψ ⊃ ◇ψ) := by
  apply ProofK.hyp
  exact ⟨ψ, rfl⟩

/--
**B axiom derivation helper**: In the context of KB axioms,
ψ ⊃ □◇ψ is provable (it's an axiom).
-/
private lemma kb_axiom {ψ : Form} :
    ProofK KBAxioms (ψ ⊃ □(◇ψ)) := by
  apply ProofK.hyp
  exact ⟨ψ, rfl⟩

------------------------------------------------------------------------------
-- § 1. Completeness for KD
------------------------------------------------------------------------------

/--
**Completeness for KD**: If φ is valid in all serial frames, then φ is provable in KD.

**Proof**: By contrapositive. If ⊬_KD φ:
1. {¬φ} is KD-consistent
2. Extend to maximal KD-consistent set w with ¬φ ∈ w
3. Show the canonical frame is serial (key step using D axiom)
4. By truth lemma, w ⊮ φ in the canonical model
5. Since the canonical frame is serial, ⊭_serial φ
-/
theorem completeness_KD (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ x, ∃ y, F.rel x y) → ∀ w, forces F v w φ) →
  ProofK KDAxioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist KDAxioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK KDAxioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK KDAxioms φ := fin_conj_repeat sem_consKD hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KDAxioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  -- Key step: Show the canonical frame is serial
  have hserial : ∀ (w' : World KDAxioms), ∃ w'', (canonicalFrame KDAxioms).rel w' w'' := by
    intro w'
    -- We need to show {ψ | □ψ ∈ w'} is consistent, then extend it
    -- If {ψ | □ψ ∈ w'} were inconsistent, then for some L ⊆ {ψ | □ψ ∈ w'},
    -- we'd have ⊢ ¬(fin_conj L), meaning ⊢ □¬(fin_conj L),
    -- meaning □⊥ ∈ w' (since □(fin_conj L) ⊃ □(something) ∈ w')
    -- But by D axiom, □⊥ ⊃ ◇⊥, and ◇⊥ is contradictory.
    have hcons_box : ax_consist KDAxioms {ψ | World.mem (□ψ) w'} := by
      intro L hall
      by_contra hcontra
      rw [fin_ax_consist] at hcontra
      push_neg at hcontra
      -- L ⊆ {ψ | □ψ ∈ w'} and ⊢ ¬(fin_conj L)
      have hall_boxed : ∀ ψ ∈ L, World.mem (□ψ) w' := hall
      -- From ⊢ ¬(fin_conj L), get ⊢ □¬(fin_conj L)
      -- Then ⊢ (fin_conj (L.map □)) ⊃ □(fin_conj L) by fin_conj_boxn
      -- And ⊢ □(fin_conj L) ⊃ □⊥ by box_mono
      -- So (fin_conj (L.map □)) ⊃ □⊥
      have hbox_bot : ProofK KDAxioms (fin_conj (L.map (□·)) ⊃ □⊥ₘ) := by
        have h1 : ProofK KDAxioms (fin_conj (L.map (□·)) ⊃ □(fin_conj L)) := fin_conj_boxn
        have h2 : ProofK KDAxioms (∼(fin_conj L)) := hcontra
        -- ∼(fin_conj L) = (fin_conj L ⊃ ⊥), so fin_conj L ⊃ ⊥
        have h3 : ProofK KDAxioms (□(fin_conj L) ⊃ □⊥ₘ) := box_mono h2
        exact cut h1 h3
      -- All formulas in L.map □ are in w'
      have hall_in_w' : ∀ χ ∈ L.map (□·), World.mem χ w' := by
        intro χ hmem
        rw [List.mem_map] at hmem
        obtain ⟨ψ, hψ_in, rfl⟩ := hmem
        exact hall_boxed ψ hψ_in
      -- So □⊥ ∈ w'
      have hbox_bot_in : World.mem (□⊥ₘ) w' :=
        World.proves w' hall_in_w' hbox_bot
      -- By D axiom, □⊥ ⊃ ◇⊥
      have hD : ProofK KDAxioms (□⊥ₘ ⊃ ◇⊥ₘ) := kd_box_to_dia
      -- So ◇⊥ ∈ w'
      have hdia_bot : World.mem (◇⊥ₘ) w' := World.derives w' hbox_bot_in hD
      -- ◇⊥ = ¬□¬⊥ = ¬□⊤ (since ¬⊥ = ⊤)
      -- □⊤ is provable (nec of identity), so □⊤ ∈ w'
      -- This contradicts ◇⊥ = ¬□⊤ ∈ w'
      have hbox_top : World.mem (□(∼⊥ₘ)) w' := by
        apply World.proves w' (L := []) (fun _ h => by cases h)
        simp [fin_conj]
        exact k_intro (nec prtrue)
      -- ◇⊥ = ∼□∼⊥ and □∼⊥ ∈ w', contradiction
      have : ¬World.mem (□(∼⊥ₘ)) w' := (World.not_mem_iff w' (□(∼⊥ₘ))).mpr hdia_bot
      exact this hbox_top

    let w'' := extendToMaximal {ψ | World.mem (□ψ) w'} hcons_box
    use ⟨w''.val, w''.property.1⟩
    intro ψ hbox
    exact w''.property.2 hbox

  have hrefute : ¬forces (canonicalFrame KDAxioms) canonicalVal w φ := by
    rw [truthLemma KDAxioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame KDAxioms) canonicalVal hserial w)

------------------------------------------------------------------------------
-- § 2. Completeness for KB
------------------------------------------------------------------------------

/--
**Completeness for KB**: If φ is valid in all symmetric frames, then φ is provable in KB.

**Proof**: By contrapositive. If ⊬_KB φ:
1. {¬φ} is KB-consistent
2. Extend to maximal KB-consistent set w with ¬φ ∈ w
3. Show the canonical frame is symmetric (key step using B axiom)
4. By truth lemma, w ⊮ φ in the canonical model
5. Since the canonical frame is symmetric, ⊭_symm φ
-/
theorem completeness_KB (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w₁ w₂, F.rel w₁ w₂ → F.rel w₂ w₁) → ∀ w, forces F v w φ) →
  ProofK KBAxioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist KBAxioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK KBAxioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK KBAxioms φ := fin_conj_repeat sem_consKB hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KBAxioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  -- Key step: Show the canonical frame is symmetric
  have hsymm : ∀ (w₁ w₂ : World KBAxioms),
      (canonicalFrame KBAxioms).rel w₁ w₂ →
      (canonicalFrame KBAxioms).rel w₂ w₁ := by
    intro w₁ w₂ hrel₁₂
    unfold canonicalFrame at *
    simp at *
    -- Need: ∀ ψ, □ψ ∈ w₂ → ψ ∈ w₁
    intro ψ hbox_ψ_w₂
    -- Suppose ψ ∉ w₁, then ¬ψ ∈ w₁
    by_contra hψ_notin_w₁
    have hneg_ψ_w₁ : World.mem (∼ψ) w₁ := (World.not_mem_iff w₁ ψ).mp hψ_notin_w₁
    -- By B axiom: ¬ψ → □◇¬ψ, so □◇¬ψ ∈ w₁
    have hB : ProofK KBAxioms (∼ψ ⊃ □(◇(∼ψ))) := kb_axiom
    have hbox_dia_neg : World.mem (□(◇(∼ψ))) w₁ :=
      World.derives w₁ hneg_ψ_w₁ hB
    -- Since w₁ R w₂, ◇¬ψ ∈ w₂
    have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ := hrel₁₂ (◇(∼ψ)) hbox_dia_neg
    -- ◇¬ψ ⊃ ¬□ψ by dia_neg_to_not_box
    have hdia_imp : ProofK KBAxioms (◇(∼ψ) ⊃ ∼(□ψ)) := dia_neg_to_not_box
    have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ :=
      World.derives w₂ hdia_neg_w₂ hdia_imp
    -- But □ψ ∈ w₂ by assumption, contradiction
    exact World.no_contradiction w₂ (□ψ) ⟨hbox_ψ_w₂, hnot_box_w₂⟩

  have hrefute : ¬forces (canonicalFrame KBAxioms) canonicalVal w φ := by
    rw [truthLemma KBAxioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame KBAxioms) canonicalVal hsymm w)

end
