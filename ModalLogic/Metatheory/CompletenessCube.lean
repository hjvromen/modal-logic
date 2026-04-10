import ModalLogic.Metatheory.Canonical

/-!
# Completeness Theorems for K4, KTB, and KB4

This file proves the completeness theorems for the remaining logics in the
modal logic cube, extending the existing completeness results.

## K4 Completeness

**K4** extends K with the 4 axiom: □φ → □□φ (transitivity).
K4 is sound and complete with respect to **transitive frames**.

**Strategy**: Show the canonical frame for K4 is transitive using the 4 axiom.

## KTB Completeness

**KTB** (Brouwerian logic) extends K with T + B axioms.
KTB is sound and complete with respect to **reflexive-symmetric frames**.

**Strategy**: Show the canonical frame for KTB is reflexive (using T)
and symmetric (using B).

## KB4 Completeness

**KB4** extends K with B + 4 axioms.
KB4 is sound and complete with respect to **symmetric-transitive frames**.

**Strategy**: Show the canonical frame for KB4 is symmetric (using B)
and transitive (using 4).
-/

open Classical
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

------------------------------------------------------------------------------
-- § 1. Completeness for K4
------------------------------------------------------------------------------

/--
**Completeness for K4**: If φ is valid in all transitive frames,
then φ is provable in K4.
-/
theorem completeness_K4 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    ∀ w, forces F v w φ) →
  ProofK K4Axioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist K4Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK K4Axioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK K4Axioms φ := fin_conj_repeat sem_consK4 hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World K4Axioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  -- Key step: Show the canonical frame is transitive
  have htrans : ∀ (w₁ w₂ w₃ : World K4Axioms),
      (canonicalFrame K4Axioms).rel w₁ w₂ →
      (canonicalFrame K4Axioms).rel w₂ w₃ →
      (canonicalFrame K4Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox
    have h4_axiom_in : (□ψ ⊃ □□ψ) ∈ K4Axioms := ⟨ψ, rfl⟩
    have h4_axiom : ProofK K4Axioms (□ψ ⊃ □□ψ) := hyp h4_axiom_in
    have h4_in_w₁ : World.mem (□ψ ⊃ □□ψ) w₁ := by
      apply World.proves w₁ (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        exact k_intro h4_axiom
    have hbox_box : World.mem (□□ψ) w₁ := World.mp w₁ h4_in_w₁ hbox
    have hbox_in_w₂ : World.mem (□ψ) w₂ := hrel₁₂ (□ψ) hbox_box
    exact hrel₂₃ ψ hbox_in_w₂

  have hrefute : ¬forces (canonicalFrame K4Axioms) canonicalVal w φ := by
    rw [truthLemma K4Axioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame K4Axioms) canonicalVal htrans w)

------------------------------------------------------------------------------
-- § 2. Completeness for KTB
------------------------------------------------------------------------------

/--
**Completeness for KTB**: If φ is valid in all reflexive-symmetric frames,
then φ is provable in KTB.
-/
theorem completeness_KTB (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w, F.rel w w) →
    (∀ w₁ w₂, F.rel w₁ w₂ → F.rel w₂ w₁) →
    ∀ w, forces F v w φ) →
  ProofK KTBAxioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist KTBAxioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK KTBAxioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK KTBAxioms φ := fin_conj_repeat sem_consKTB hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KTBAxioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  -- Key step 1: Show the canonical frame is reflexive (from T axiom)
  have hrefl : ∀ (w' : World KTBAxioms), (canonicalFrame KTBAxioms).rel w' w' := by
    intro w'
    unfold canonicalFrame
    simp
    intro ψ hbox
    have hT_in_axioms : (□ψ ⊃ ψ) ∈ KTBAxioms := by left; exact ⟨ψ, rfl⟩
    have hT_axiom : ProofK KTBAxioms (□ψ ⊃ ψ) := hyp hT_in_axioms
    have hT_imp_in_w' : World.mem (□ψ ⊃ ψ) w' := by
      apply World.proves w' (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        exact k_intro hT_axiom
    exact World.mp w' hT_imp_in_w' hbox

  -- Key step 2: Show the canonical frame is symmetric (from B axiom)
  have hsymm : ∀ (w₁ w₂ : World KTBAxioms),
      (canonicalFrame KTBAxioms).rel w₁ w₂ →
      (canonicalFrame KTBAxioms).rel w₂ w₁ := by
    intro w₁ w₂ hrel₁₂
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox_ψ_w₂
    by_contra hψ_notin_w₁
    have hneg_ψ_w₁ : World.mem (∼ψ) w₁ := (World.not_mem_iff w₁ ψ).mp hψ_notin_w₁
    have hB : ProofK KTBAxioms (∼ψ ⊃ □(◇(∼ψ))) := by
      apply ProofK.hyp
      right
      exact ⟨∼ψ, rfl⟩
    have hbox_dia_neg : World.mem (□(◇(∼ψ))) w₁ :=
      World.derives w₁ hneg_ψ_w₁ hB
    have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ := hrel₁₂ (◇(∼ψ)) hbox_dia_neg
    have hdia_imp : ProofK KTBAxioms (◇(∼ψ) ⊃ ∼(□ψ)) := dia_neg_to_not_box
    have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ :=
      World.derives w₂ hdia_neg_w₂ hdia_imp
    exact World.no_contradiction w₂ (□ψ) ⟨hbox_ψ_w₂, hnot_box_w₂⟩

  have hrefute : ¬forces (canonicalFrame KTBAxioms) canonicalVal w φ := by
    rw [truthLemma KTBAxioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame KTBAxioms) canonicalVal hrefl hsymm w)

------------------------------------------------------------------------------
-- § 3. Completeness for KB4
------------------------------------------------------------------------------

/--
**Completeness for KB4**: If φ is valid in all symmetric-transitive frames,
then φ is provable in KB4.
-/
theorem completeness_KB4 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w₁ w₂, F.rel w₁ w₂ → F.rel w₂ w₁) →
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    ∀ w, forces F v w φ) →
  ProofK KB4Axioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist KB4Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK KB4Axioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK KB4Axioms φ := fin_conj_repeat sem_consKB4 hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KB4Axioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  -- Key step 1: Show the canonical frame is symmetric (from B axiom)
  have hsymm : ∀ (w₁ w₂ : World KB4Axioms),
      (canonicalFrame KB4Axioms).rel w₁ w₂ →
      (canonicalFrame KB4Axioms).rel w₂ w₁ := by
    intro w₁ w₂ hrel₁₂
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox_ψ_w₂
    by_contra hψ_notin_w₁
    have hneg_ψ_w₁ : World.mem (∼ψ) w₁ := (World.not_mem_iff w₁ ψ).mp hψ_notin_w₁
    have hB : ProofK KB4Axioms (∼ψ ⊃ □(◇(∼ψ))) := by
      apply ProofK.hyp
      left
      exact ⟨∼ψ, rfl⟩
    have hbox_dia_neg : World.mem (□(◇(∼ψ))) w₁ :=
      World.derives w₁ hneg_ψ_w₁ hB
    have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ := hrel₁₂ (◇(∼ψ)) hbox_dia_neg
    have hdia_imp : ProofK KB4Axioms (◇(∼ψ) ⊃ ∼(□ψ)) := dia_neg_to_not_box
    have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ :=
      World.derives w₂ hdia_neg_w₂ hdia_imp
    exact World.no_contradiction w₂ (□ψ) ⟨hbox_ψ_w₂, hnot_box_w₂⟩

  -- Key step 2: Show the canonical frame is transitive (from 4 axiom)
  have htrans : ∀ (w₁ w₂ w₃ : World KB4Axioms),
      (canonicalFrame KB4Axioms).rel w₁ w₂ →
      (canonicalFrame KB4Axioms).rel w₂ w₃ →
      (canonicalFrame KB4Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox
    have h4_axiom_in : (□ψ ⊃ □□ψ) ∈ KB4Axioms := by right; exact ⟨ψ, rfl⟩
    have h4_axiom : ProofK KB4Axioms (□ψ ⊃ □□ψ) := hyp h4_axiom_in
    have h4_in_w₁ : World.mem (□ψ ⊃ □□ψ) w₁ := by
      apply World.proves w₁ (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        exact k_intro h4_axiom
    have hbox_box : World.mem (□□ψ) w₁ := World.mp w₁ h4_in_w₁ hbox
    have hbox_in_w₂ : World.mem (□ψ) w₂ := hrel₁₂ (□ψ) hbox_box
    exact hrel₂₃ ψ hbox_in_w₂

  have hrefute : ¬forces (canonicalFrame KB4Axioms) canonicalVal w φ := by
    rw [truthLemma KB4Axioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame KB4Axioms) canonicalVal hsymm htrans w)

------------------------------------------------------------------------------
-- § 4. Completeness for K5
------------------------------------------------------------------------------

/--
**Completeness for K5**: If φ is valid in all Euclidean frames,
then φ is provable in K5.
-/
theorem completeness_K5 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ x y z, F.rel x y → F.rel x z → F.rel y z) →
    ∀ w, forces F v w φ) →
  ProofK K5Axioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist K5Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK K5Axioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK K5Axioms φ := fin_conj_repeat sem_consK5 hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World K5Axioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  -- Key step: Show the canonical frame is Euclidean
  have heuclid : ∀ (w₁ w₂ w₃ : World K5Axioms),
      (canonicalFrame K5Axioms).rel w₁ w₂ →
      (canonicalFrame K5Axioms).rel w₁ w₃ →
      (canonicalFrame K5Axioms).rel w₂ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₁₃
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox_w₂
    -- We need to show ψ ∈ w₃.
    -- Suppose ψ ∉ w₃ for contradiction.
    by_contra hψ_notin_w₃
    have hneg_ψ_w₃ : World.mem (∼ψ) w₃ := (World.not_mem_iff w₃ ψ).mp hψ_notin_w₃
    -- From □ψ ∈ w₂, we want to derive a contradiction.
    -- Using the 5 axiom (◇φ ⊃ □◇φ):
    -- Since □ψ ∈ w₂, and we want to show ψ ∈ w₃.
    -- Using the 5 axiom for ∼ψ: ◇∼ψ ⊃ □◇∼ψ
    -- Since ∼ψ ∈ w₃ and w₁ R w₃: ◇∼ψ holds at w₁? Not directly.
    -- In canonical models, w₁ R w₃ means ∀ χ, □χ ∈ w₁ → χ ∈ w₃.
    -- We need ◇∼ψ ∈ w₁. This means ∼□∼∼ψ = ∼□ψ (up to DNE) ∈ w₁.
    -- If □ψ ∉ w₁, then ∼□ψ ∈ w₁, which gives ◇∼ψ ∈ w₁ (since ◇φ = ∼□∼φ, we need ◇∼ψ = ∼□∼∼ψ = ∼□ψ via DNE).
    -- Then by 5: □◇∼ψ ∈ w₁.
    -- Since w₁ R w₂: ◇∼ψ ∈ w₂.
    -- ◇∼ψ ∈ w₂ means ∼□∼∼ψ ∈ w₂ = ∼□ψ ∈ w₂ (via DNE).
    -- But □ψ ∈ w₂, contradiction.
    -- If □ψ ∈ w₁, then since w₁ R w₃: ψ ∈ w₃. But ∼ψ ∈ w₃. Contradiction.
    -- So in either case we get a contradiction.
    by_cases hBoxW1 : World.mem (□ψ) w₁
    · -- Case: □ψ ∈ w₁
      have hψ_w₃ : World.mem ψ w₃ := hrel₁₃ ψ hBoxW1
      exact World.no_contradiction w₃ ψ ⟨hψ_w₃, hneg_ψ_w₃⟩
    · -- Case: □ψ ∉ w₁, so ∼□ψ ∈ w₁
      have hnot_box_w₁ : World.mem (∼(□ψ)) w₁ :=
        (World.not_mem_iff w₁ (□ψ)).mp hBoxW1
      -- ∼□ψ ∈ w₁. We need ◇∼ψ ∈ w₁ which is ∼□∼∼ψ ∈ w₁.
      -- By DNE: □∼∼ψ ⊃ □ψ (provable), so ∼□ψ ⊃ ∼□∼∼ψ
      have hdia_neg : World.mem (◇(∼ψ)) w₁ := by
        -- ◇∼ψ = ∼□∼∼ψ, and ∼□ψ ∈ w₁
        -- We have □∼∼ψ ⊃ □ψ provable (box_mono applied to DNE)
        -- So ∼□ψ ⊃ ∼□∼∼ψ (contrapositive)
        have h_imp : ProofK K5Axioms (∼(□ψ) ⊃ ◇(∼ψ)) := not_box_to_dia_neg
        exact World.derives w₁ hnot_box_w₁ h_imp
      -- By 5 axiom: ◇∼ψ ⊃ □◇∼ψ
      have h5 : ProofK K5Axioms (◇(∼ψ) ⊃ □(◇(∼ψ))) := by
        apply ProofK.hyp
        exact ⟨∼ψ, rfl⟩
      have hbox_dia_neg_w₁ : World.mem (□(◇(∼ψ))) w₁ :=
        World.derives w₁ hdia_neg h5
      -- Since w₁ R w₂: ◇∼ψ ∈ w₂
      have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ :=
        hrel₁₂ (◇(∼ψ)) hbox_dia_neg_w₁
      -- ◇∼ψ ∈ w₂ means ∼□∼∼ψ ∈ w₂
      -- By DNE: □∼∼ψ ⊃ □ψ, so ∼□ψ ⊃ ∼□∼∼ψ = ◇∼ψ
      -- So ◇∼ψ implies ∼□ψ
      have h_imp2 : ProofK K5Axioms (◇(∼ψ) ⊃ ∼(□ψ)) := dia_neg_to_not_box
      have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ :=
        World.derives w₂ hdia_neg_w₂ h_imp2
      -- But □ψ ∈ w₂ by assumption
      exact World.no_contradiction w₂ (□ψ) ⟨hbox_w₂, hnot_box_w₂⟩

  have hrefute : ¬forces (canonicalFrame K5Axioms) canonicalVal w φ := by
    rw [truthLemma K5Axioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame K5Axioms) canonicalVal heuclid w)

end
