import ModalLogic.Metatheory.Canonical

/-!
# Completeness Theorems for KDB, KD4, KD5, K45, KB5, and KD45

This file proves the completeness theorems for the six remaining modal logics
that complete the full enumeration of 16 distinct normal modal logics from
{T, B, 4, D, 5}.

Each proof follows the standard canonical model approach:
1. Assume φ is not provable
2. Extend {¬φ} to a maximal consistent set
3. Show the canonical frame has the required properties (using the axioms)
4. Derive a contradiction via the truth lemma

The frame property proofs reuse the same patterns established for the
classical cube logics:
- **Serial** (from D): same as in `completeness_KD`
- **Symmetric** (from B): same as in `completeness_KB`
- **Transitive** (from 4): same as in `completeness_K4`
- **Euclidean** (from 5): same as in `completeness_K5`
-/

open Classical
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

------------------------------------------------------------------------------
-- § 1. Completeness for KD5 (serial + Euclidean)
------------------------------------------------------------------------------

/--
**Completeness for KD5**: If φ is valid in all serial Euclidean frames,
then φ is provable in KD5.
-/
theorem completeness_KD5 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ x, ∃ y, F.rel x y) →
    (∀ x y z, F.rel x y → F.rel x z → F.rel y z) →
    ∀ w, forces F v w φ) →
  ProofK KD5Axioms φ := by
  intro hvalid
  by_contra hnot_prf
  have hcons : ax_consist KD5Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := fun ψ hmem => Set.mem_singleton_iff.mp (hall ψ hmem)
    exact hnot_prf (fin_conj_repeat sem_consKD5 hL_subset hcontra)
  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KD5Axioms := ⟨w_subtype.val, w_subtype.property.1⟩
  have hneg_φ : World.mem (∼φ) w := w_subtype.property.2 (Set.mem_singleton (∼φ))
  -- Serial (from D axiom)
  have hserial : ∀ (w' : World KD5Axioms), ∃ w'', (canonicalFrame KD5Axioms).rel w' w'' := by
    intro w'
    have hcons_box : ax_consist KD5Axioms {ψ | World.mem (□ψ) w'} := by
      intro L hall
      by_contra hcontra
      rw [fin_ax_consist] at hcontra
      push_neg at hcontra
      have hall_boxed : ∀ ψ ∈ L, World.mem (□ψ) w' := hall
      have hbox_bot : ProofK KD5Axioms (fin_conj (L.map (□·)) ⊃ □⊥ₘ) := by
        exact cut fin_conj_boxn (box_mono hcontra)
      have hall_in_w' : ∀ χ ∈ L.map (□·), World.mem χ w' := by
        intro χ hmem
        rw [List.mem_map] at hmem
        obtain ⟨ψ, hψ_in, rfl⟩ := hmem
        exact hall_boxed ψ hψ_in
      have hbox_bot_in : World.mem (□⊥ₘ) w' := World.proves w' hall_in_w' hbox_bot
      have hD : ProofK KD5Axioms (□⊥ₘ ⊃ ◇⊥ₘ) := by
        apply ProofK.hyp; left; exact ⟨⊥ₘ, rfl⟩
      have hdia_bot : World.mem (◇⊥ₘ) w' := World.derives w' hbox_bot_in hD
      have hbox_top : World.mem (□(∼⊥ₘ)) w' := by
        apply World.proves w' (L := []) (fun _ h => by cases h)
        simp [fin_conj]
        exact k_intro (nec prtrue)
      have : ¬World.mem (□(∼⊥ₘ)) w' := (World.not_mem_iff w' (□(∼⊥ₘ))).mpr hdia_bot
      exact this hbox_top
    let w'' := extendToMaximal {ψ | World.mem (□ψ) w'} hcons_box
    use ⟨w''.val, w''.property.1⟩
    intro ψ hbox
    exact w''.property.2 hbox
  -- Euclidean (from 5 axiom)
  have heuclid : ∀ (w₁ w₂ w₃ : World KD5Axioms),
      (canonicalFrame KD5Axioms).rel w₁ w₂ →
      (canonicalFrame KD5Axioms).rel w₁ w₃ →
      (canonicalFrame KD5Axioms).rel w₂ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₁₃
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox_w₂
    by_contra hψ_notin_w₃
    have hneg_ψ_w₃ : World.mem (∼ψ) w₃ := (World.not_mem_iff w₃ ψ).mp hψ_notin_w₃
    by_cases hBoxW1 : World.mem (□ψ) w₁
    · have hψ_w₃ : World.mem ψ w₃ := hrel₁₃ ψ hBoxW1
      exact World.no_contradiction w₃ ψ ⟨hψ_w₃, hneg_ψ_w₃⟩
    · have hnot_box_w₁ : World.mem (∼(□ψ)) w₁ := (World.not_mem_iff w₁ (□ψ)).mp hBoxW1
      have hdia_neg : World.mem (◇(∼ψ)) w₁ := by
        exact World.derives w₁ hnot_box_w₁ not_box_to_dia_neg
      have h5 : ProofK KD5Axioms (◇(∼ψ) ⊃ □(◇(∼ψ))) := by
        apply ProofK.hyp; right; exact ⟨∼ψ, rfl⟩
      have hbox_dia_neg_w₁ : World.mem (□(◇(∼ψ))) w₁ := World.derives w₁ hdia_neg h5
      have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ := hrel₁₂ (◇(∼ψ)) hbox_dia_neg_w₁
      have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ := World.derives w₂ hdia_neg_w₂ dia_neg_to_not_box
      exact World.no_contradiction w₂ (□ψ) ⟨hbox_w₂, hnot_box_w₂⟩
  have hrefute : ¬forces (canonicalFrame KD5Axioms) canonicalVal w φ := by
    rw [truthLemma KD5Axioms w]
    exact fun hφ => (World.not_mem_iff w φ).mpr hneg_φ hφ
  exact hrefute (hvalid (canonicalFrame KD5Axioms) canonicalVal hserial heuclid w)

------------------------------------------------------------------------------
-- § 2. Completeness for KD45 (serial + transitive + Euclidean)
------------------------------------------------------------------------------

/--
**Completeness for KD45**: If φ is valid in all serial transitive Euclidean frames,
then φ is provable in KD45.
-/
theorem completeness_KD45 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ x, ∃ y, F.rel x y) →
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    (∀ x y z, F.rel x y → F.rel x z → F.rel y z) →
    ∀ w, forces F v w φ) →
  ProofK KD45Axioms φ := by
  intro hvalid
  by_contra hnot_prf
  have hcons : ax_consist KD45Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := fun ψ hmem => Set.mem_singleton_iff.mp (hall ψ hmem)
    exact hnot_prf (fin_conj_repeat sem_consKD45 hL_subset hcontra)
  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KD45Axioms := ⟨w_subtype.val, w_subtype.property.1⟩
  have hneg_φ : World.mem (∼φ) w := w_subtype.property.2 (Set.mem_singleton (∼φ))
  -- Serial (from D axiom)
  have hserial : ∀ (w' : World KD45Axioms), ∃ w'', (canonicalFrame KD45Axioms).rel w' w'' := by
    intro w'
    have hcons_box : ax_consist KD45Axioms {ψ | World.mem (□ψ) w'} := by
      intro L hall
      by_contra hcontra
      rw [fin_ax_consist] at hcontra
      push_neg at hcontra
      have hall_boxed : ∀ ψ ∈ L, World.mem (□ψ) w' := hall
      have hbox_bot : ProofK KD45Axioms (fin_conj (L.map (□·)) ⊃ □⊥ₘ) :=
        cut fin_conj_boxn (box_mono hcontra)
      have hall_in_w' : ∀ χ ∈ L.map (□·), World.mem χ w' := by
        intro χ hmem
        rw [List.mem_map] at hmem
        obtain ⟨ψ, hψ_in, rfl⟩ := hmem
        exact hall_boxed ψ hψ_in
      have hbox_bot_in : World.mem (□⊥ₘ) w' := World.proves w' hall_in_w' hbox_bot
      have hD : ProofK KD45Axioms (□⊥ₘ ⊃ ◇⊥ₘ) := by
        apply ProofK.hyp; left; left; exact ⟨⊥ₘ, rfl⟩
      have hdia_bot : World.mem (◇⊥ₘ) w' := World.derives w' hbox_bot_in hD
      have hbox_top : World.mem (□(∼⊥ₘ)) w' := by
        apply World.proves w' (L := []) (fun _ h => by cases h)
        simp [fin_conj]
        exact k_intro (nec prtrue)
      exact (World.not_mem_iff w' (□(∼⊥ₘ))).mpr hdia_bot hbox_top
    let w'' := extendToMaximal {ψ | World.mem (□ψ) w'} hcons_box
    use ⟨w''.val, w''.property.1⟩
    intro ψ hbox
    exact w''.property.2 hbox
  -- Transitive (from 4 axiom)
  have htrans : ∀ (w₁ w₂ w₃ : World KD45Axioms),
      (canonicalFrame KD45Axioms).rel w₁ w₂ →
      (canonicalFrame KD45Axioms).rel w₂ w₃ →
      (canonicalFrame KD45Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    unfold canonicalFrame at *; simp at *
    intro ψ hbox
    have h4_in : (□ψ ⊃ □□ψ) ∈ KD45Axioms := by left; right; exact ⟨ψ, rfl⟩
    have h4_in_w₁ : World.mem (□ψ ⊃ □□ψ) w₁ := by
      apply World.proves w₁ (L := []) (fun _ h => by cases h)
      simp [fin_conj]; exact k_intro (hyp h4_in)
    exact hrel₂₃ ψ (hrel₁₂ (□ψ) (World.mp w₁ h4_in_w₁ hbox))
  -- Euclidean (from 5 axiom)
  have heuclid : ∀ (w₁ w₂ w₃ : World KD45Axioms),
      (canonicalFrame KD45Axioms).rel w₁ w₂ →
      (canonicalFrame KD45Axioms).rel w₁ w₃ →
      (canonicalFrame KD45Axioms).rel w₂ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₁₃
    unfold canonicalFrame at *; simp at *
    intro ψ hbox_w₂
    by_contra hψ_notin_w₃
    have hneg_ψ_w₃ : World.mem (∼ψ) w₃ := (World.not_mem_iff w₃ ψ).mp hψ_notin_w₃
    by_cases hBoxW1 : World.mem (□ψ) w₁
    · exact World.no_contradiction w₃ ψ ⟨hrel₁₃ ψ hBoxW1, hneg_ψ_w₃⟩
    · have hnot_box_w₁ : World.mem (∼(□ψ)) w₁ := (World.not_mem_iff w₁ (□ψ)).mp hBoxW1
      have hdia_neg : World.mem (◇(∼ψ)) w₁ := World.derives w₁ hnot_box_w₁ not_box_to_dia_neg
      have h5 : ProofK KD45Axioms (◇(∼ψ) ⊃ □(◇(∼ψ))) := by
        apply ProofK.hyp; right; exact ⟨∼ψ, rfl⟩
      have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ :=
        hrel₁₂ (◇(∼ψ)) (World.derives w₁ hdia_neg h5)
      exact World.no_contradiction w₂ (□ψ) ⟨hbox_w₂, World.derives w₂ hdia_neg_w₂ dia_neg_to_not_box⟩
  have hrefute : ¬forces (canonicalFrame KD45Axioms) canonicalVal w φ := by
    rw [truthLemma KD45Axioms w]
    exact fun hφ => (World.not_mem_iff w φ).mpr hneg_φ hφ
  exact hrefute (hvalid (canonicalFrame KD45Axioms) canonicalVal hserial htrans heuclid w)

------------------------------------------------------------------------------
-- § 3. Completeness for KDB (serial + symmetric)
------------------------------------------------------------------------------

/--
**Completeness for KDB**: If φ is valid in all serial symmetric frames,
then φ is provable in KDB.
-/
theorem completeness_KDB (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ x, ∃ y, F.rel x y) →
    (∀ w₁ w₂, F.rel w₁ w₂ → F.rel w₂ w₁) →
    ∀ w, forces F v w φ) →
  ProofK KDBAxioms φ := by
  intro hvalid
  by_contra hnot_prf
  have hcons : ax_consist KDBAxioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := fun ψ hmem => Set.mem_singleton_iff.mp (hall ψ hmem)
    exact hnot_prf (fin_conj_repeat sem_consKDB hL_subset hcontra)
  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KDBAxioms := ⟨w_subtype.val, w_subtype.property.1⟩
  have hneg_φ : World.mem (∼φ) w := w_subtype.property.2 (Set.mem_singleton (∼φ))
  -- Serial (from D axiom)
  have hserial : ∀ (w' : World KDBAxioms), ∃ w'', (canonicalFrame KDBAxioms).rel w' w'' := by
    intro w'
    have hcons_box : ax_consist KDBAxioms {ψ | World.mem (□ψ) w'} := by
      intro L hall
      by_contra hcontra
      rw [fin_ax_consist] at hcontra
      push_neg at hcontra
      have hall_boxed : ∀ ψ ∈ L, World.mem (□ψ) w' := hall
      have hbox_bot : ProofK KDBAxioms (fin_conj (L.map (□·)) ⊃ □⊥ₘ) :=
        cut fin_conj_boxn (box_mono hcontra)
      have hall_in_w' : ∀ χ ∈ L.map (□·), World.mem χ w' := by
        intro χ hmem
        rw [List.mem_map] at hmem
        obtain ⟨ψ, hψ_in, rfl⟩ := hmem
        exact hall_boxed ψ hψ_in
      have hbox_bot_in : World.mem (□⊥ₘ) w' := World.proves w' hall_in_w' hbox_bot
      have hD : ProofK KDBAxioms (□⊥ₘ ⊃ ◇⊥ₘ) := by
        apply ProofK.hyp; left; exact ⟨⊥ₘ, rfl⟩
      have hdia_bot : World.mem (◇⊥ₘ) w' := World.derives w' hbox_bot_in hD
      have hbox_top : World.mem (□(∼⊥ₘ)) w' := by
        apply World.proves w' (L := []) (fun _ h => by cases h)
        simp [fin_conj]; exact k_intro (nec prtrue)
      exact (World.not_mem_iff w' (□(∼⊥ₘ))).mpr hdia_bot hbox_top
    let w'' := extendToMaximal {ψ | World.mem (□ψ) w'} hcons_box
    use ⟨w''.val, w''.property.1⟩
    intro ψ hbox
    exact w''.property.2 hbox
  -- Symmetric (from B axiom)
  have hsymm : ∀ (w₁ w₂ : World KDBAxioms),
      (canonicalFrame KDBAxioms).rel w₁ w₂ →
      (canonicalFrame KDBAxioms).rel w₂ w₁ := by
    intro w₁ w₂ hrel₁₂
    unfold canonicalFrame at *; simp at *
    intro ψ hbox_ψ_w₂
    by_contra hψ_notin_w₁
    have hneg_ψ_w₁ : World.mem (∼ψ) w₁ := (World.not_mem_iff w₁ ψ).mp hψ_notin_w₁
    have hB : ProofK KDBAxioms (∼ψ ⊃ □(◇(∼ψ))) := by
      apply ProofK.hyp; right; exact ⟨∼ψ, rfl⟩
    have hbox_dia_neg : World.mem (□(◇(∼ψ))) w₁ := World.derives w₁ hneg_ψ_w₁ hB
    have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ := hrel₁₂ (◇(∼ψ)) hbox_dia_neg
    have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ := World.derives w₂ hdia_neg_w₂ dia_neg_to_not_box
    exact World.no_contradiction w₂ (□ψ) ⟨hbox_ψ_w₂, hnot_box_w₂⟩
  have hrefute : ¬forces (canonicalFrame KDBAxioms) canonicalVal w φ := by
    rw [truthLemma KDBAxioms w]
    exact fun hφ => (World.not_mem_iff w φ).mpr hneg_φ hφ
  exact hrefute (hvalid (canonicalFrame KDBAxioms) canonicalVal hserial hsymm w)

------------------------------------------------------------------------------
-- § 4. Completeness for KD4 (serial + transitive)
------------------------------------------------------------------------------

/--
**Completeness for KD4**: If φ is valid in all serial transitive frames,
then φ is provable in KD4.
-/
theorem completeness_KD4 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ x, ∃ y, F.rel x y) →
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    ∀ w, forces F v w φ) →
  ProofK KD4Axioms φ := by
  intro hvalid
  by_contra hnot_prf
  have hcons : ax_consist KD4Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := fun ψ hmem => Set.mem_singleton_iff.mp (hall ψ hmem)
    exact hnot_prf (fin_conj_repeat sem_consKD4 hL_subset hcontra)
  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KD4Axioms := ⟨w_subtype.val, w_subtype.property.1⟩
  have hneg_φ : World.mem (∼φ) w := w_subtype.property.2 (Set.mem_singleton (∼φ))
  -- Serial (from D axiom)
  have hserial : ∀ (w' : World KD4Axioms), ∃ w'', (canonicalFrame KD4Axioms).rel w' w'' := by
    intro w'
    have hcons_box : ax_consist KD4Axioms {ψ | World.mem (□ψ) w'} := by
      intro L hall
      by_contra hcontra
      rw [fin_ax_consist] at hcontra
      push_neg at hcontra
      have hall_boxed : ∀ ψ ∈ L, World.mem (□ψ) w' := hall
      have hbox_bot : ProofK KD4Axioms (fin_conj (L.map (□·)) ⊃ □⊥ₘ) :=
        cut fin_conj_boxn (box_mono hcontra)
      have hall_in_w' : ∀ χ ∈ L.map (□·), World.mem χ w' := by
        intro χ hmem
        rw [List.mem_map] at hmem
        obtain ⟨ψ, hψ_in, rfl⟩ := hmem
        exact hall_boxed ψ hψ_in
      have hbox_bot_in : World.mem (□⊥ₘ) w' := World.proves w' hall_in_w' hbox_bot
      have hD : ProofK KD4Axioms (□⊥ₘ ⊃ ◇⊥ₘ) := by
        apply ProofK.hyp; left; exact ⟨⊥ₘ, rfl⟩
      have hdia_bot : World.mem (◇⊥ₘ) w' := World.derives w' hbox_bot_in hD
      have hbox_top : World.mem (□(∼⊥ₘ)) w' := by
        apply World.proves w' (L := []) (fun _ h => by cases h)
        simp [fin_conj]; exact k_intro (nec prtrue)
      exact (World.not_mem_iff w' (□(∼⊥ₘ))).mpr hdia_bot hbox_top
    let w'' := extendToMaximal {ψ | World.mem (□ψ) w'} hcons_box
    use ⟨w''.val, w''.property.1⟩
    intro ψ hbox
    exact w''.property.2 hbox
  -- Transitive (from 4 axiom)
  have htrans : ∀ (w₁ w₂ w₃ : World KD4Axioms),
      (canonicalFrame KD4Axioms).rel w₁ w₂ →
      (canonicalFrame KD4Axioms).rel w₂ w₃ →
      (canonicalFrame KD4Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    unfold canonicalFrame at *; simp at *
    intro ψ hbox
    have h4_in : (□ψ ⊃ □□ψ) ∈ KD4Axioms := by right; exact ⟨ψ, rfl⟩
    have h4_in_w₁ : World.mem (□ψ ⊃ □□ψ) w₁ := by
      apply World.proves w₁ (L := []) (fun _ h => by cases h)
      simp [fin_conj]; exact k_intro (hyp h4_in)
    exact hrel₂₃ ψ (hrel₁₂ (□ψ) (World.mp w₁ h4_in_w₁ hbox))
  have hrefute : ¬forces (canonicalFrame KD4Axioms) canonicalVal w φ := by
    rw [truthLemma KD4Axioms w]
    exact fun hφ => (World.not_mem_iff w φ).mpr hneg_φ hφ
  exact hrefute (hvalid (canonicalFrame KD4Axioms) canonicalVal hserial htrans w)

------------------------------------------------------------------------------
-- § 5. Completeness for K45 (transitive + Euclidean)
------------------------------------------------------------------------------

/--
**Completeness for K45**: If φ is valid in all transitive Euclidean frames,
then φ is provable in K45.
-/
theorem completeness_K45 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    (∀ x y z, F.rel x y → F.rel x z → F.rel y z) →
    ∀ w, forces F v w φ) →
  ProofK K45Axioms φ := by
  intro hvalid
  by_contra hnot_prf
  have hcons : ax_consist K45Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := fun ψ hmem => Set.mem_singleton_iff.mp (hall ψ hmem)
    exact hnot_prf (fin_conj_repeat sem_consK45 hL_subset hcontra)
  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World K45Axioms := ⟨w_subtype.val, w_subtype.property.1⟩
  have hneg_φ : World.mem (∼φ) w := w_subtype.property.2 (Set.mem_singleton (∼φ))
  -- Transitive (from 4 axiom)
  have htrans : ∀ (w₁ w₂ w₃ : World K45Axioms),
      (canonicalFrame K45Axioms).rel w₁ w₂ →
      (canonicalFrame K45Axioms).rel w₂ w₃ →
      (canonicalFrame K45Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    unfold canonicalFrame at *; simp at *
    intro ψ hbox
    have h4_in : (□ψ ⊃ □□ψ) ∈ K45Axioms := by left; exact ⟨ψ, rfl⟩
    have h4_in_w₁ : World.mem (□ψ ⊃ □□ψ) w₁ := by
      apply World.proves w₁ (L := []) (fun _ h => by cases h)
      simp [fin_conj]; exact k_intro (hyp h4_in)
    exact hrel₂₃ ψ (hrel₁₂ (□ψ) (World.mp w₁ h4_in_w₁ hbox))
  -- Euclidean (from 5 axiom)
  have heuclid : ∀ (w₁ w₂ w₃ : World K45Axioms),
      (canonicalFrame K45Axioms).rel w₁ w₂ →
      (canonicalFrame K45Axioms).rel w₁ w₃ →
      (canonicalFrame K45Axioms).rel w₂ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₁₃
    unfold canonicalFrame at *; simp at *
    intro ψ hbox_w₂
    by_contra hψ_notin_w₃
    have hneg_ψ_w₃ : World.mem (∼ψ) w₃ := (World.not_mem_iff w₃ ψ).mp hψ_notin_w₃
    by_cases hBoxW1 : World.mem (□ψ) w₁
    · exact World.no_contradiction w₃ ψ ⟨hrel₁₃ ψ hBoxW1, hneg_ψ_w₃⟩
    · have hnot_box_w₁ : World.mem (∼(□ψ)) w₁ := (World.not_mem_iff w₁ (□ψ)).mp hBoxW1
      have hdia_neg : World.mem (◇(∼ψ)) w₁ := World.derives w₁ hnot_box_w₁ not_box_to_dia_neg
      have h5 : ProofK K45Axioms (◇(∼ψ) ⊃ □(◇(∼ψ))) := by
        apply ProofK.hyp; right; exact ⟨∼ψ, rfl⟩
      have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ :=
        hrel₁₂ (◇(∼ψ)) (World.derives w₁ hdia_neg h5)
      exact World.no_contradiction w₂ (□ψ) ⟨hbox_w₂, World.derives w₂ hdia_neg_w₂ dia_neg_to_not_box⟩
  have hrefute : ¬forces (canonicalFrame K45Axioms) canonicalVal w φ := by
    rw [truthLemma K45Axioms w]
    exact fun hφ => (World.not_mem_iff w φ).mpr hneg_φ hφ
  exact hrefute (hvalid (canonicalFrame K45Axioms) canonicalVal htrans heuclid w)

------------------------------------------------------------------------------
-- § 6. Completeness for KB5 (symmetric + Euclidean)
------------------------------------------------------------------------------

/--
**Completeness for KB5**: If φ is valid in all symmetric Euclidean frames,
then φ is provable in KB5.
-/
theorem completeness_KB5 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w₁ w₂, F.rel w₁ w₂ → F.rel w₂ w₁) →
    (∀ x y z, F.rel x y → F.rel x z → F.rel y z) →
    ∀ w, forces F v w φ) →
  ProofK KB5Axioms φ := by
  intro hvalid
  by_contra hnot_prf
  have hcons : ax_consist KB5Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := fun ψ hmem => Set.mem_singleton_iff.mp (hall ψ hmem)
    exact hnot_prf (fin_conj_repeat sem_consKB5 hL_subset hcontra)
  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World KB5Axioms := ⟨w_subtype.val, w_subtype.property.1⟩
  have hneg_φ : World.mem (∼φ) w := w_subtype.property.2 (Set.mem_singleton (∼φ))
  -- Symmetric (from B axiom)
  have hsymm : ∀ (w₁ w₂ : World KB5Axioms),
      (canonicalFrame KB5Axioms).rel w₁ w₂ →
      (canonicalFrame KB5Axioms).rel w₂ w₁ := by
    intro w₁ w₂ hrel₁₂
    unfold canonicalFrame at *; simp at *
    intro ψ hbox_ψ_w₂
    by_contra hψ_notin_w₁
    have hneg_ψ_w₁ : World.mem (∼ψ) w₁ := (World.not_mem_iff w₁ ψ).mp hψ_notin_w₁
    have hB : ProofK KB5Axioms (∼ψ ⊃ □(◇(∼ψ))) := by
      apply ProofK.hyp; left; exact ⟨∼ψ, rfl⟩
    have hbox_dia_neg : World.mem (□(◇(∼ψ))) w₁ := World.derives w₁ hneg_ψ_w₁ hB
    have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ := hrel₁₂ (◇(∼ψ)) hbox_dia_neg
    have hnot_box_w₂ : World.mem (∼(□ψ)) w₂ := World.derives w₂ hdia_neg_w₂ dia_neg_to_not_box
    exact World.no_contradiction w₂ (□ψ) ⟨hbox_ψ_w₂, hnot_box_w₂⟩
  -- Euclidean (from 5 axiom)
  have heuclid : ∀ (w₁ w₂ w₃ : World KB5Axioms),
      (canonicalFrame KB5Axioms).rel w₁ w₂ →
      (canonicalFrame KB5Axioms).rel w₁ w₃ →
      (canonicalFrame KB5Axioms).rel w₂ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₁₃
    unfold canonicalFrame at *; simp at *
    intro ψ hbox_w₂
    by_contra hψ_notin_w₃
    have hneg_ψ_w₃ : World.mem (∼ψ) w₃ := (World.not_mem_iff w₃ ψ).mp hψ_notin_w₃
    by_cases hBoxW1 : World.mem (□ψ) w₁
    · exact World.no_contradiction w₃ ψ ⟨hrel₁₃ ψ hBoxW1, hneg_ψ_w₃⟩
    · have hnot_box_w₁ : World.mem (∼(□ψ)) w₁ := (World.not_mem_iff w₁ (□ψ)).mp hBoxW1
      have hdia_neg : World.mem (◇(∼ψ)) w₁ := World.derives w₁ hnot_box_w₁ not_box_to_dia_neg
      have h5 : ProofK KB5Axioms (◇(∼ψ) ⊃ □(◇(∼ψ))) := by
        apply ProofK.hyp; right; exact ⟨∼ψ, rfl⟩
      have hdia_neg_w₂ : World.mem (◇(∼ψ)) w₂ :=
        hrel₁₂ (◇(∼ψ)) (World.derives w₁ hdia_neg h5)
      exact World.no_contradiction w₂ (□ψ) ⟨hbox_w₂, World.derives w₂ hdia_neg_w₂ dia_neg_to_not_box⟩
  have hrefute : ¬forces (canonicalFrame KB5Axioms) canonicalVal w φ := by
    rw [truthLemma KB5Axioms w]
    exact fun hφ => (World.not_mem_iff w φ).mpr hneg_φ hφ
  exact hrefute (hvalid (canonicalFrame KB5Axioms) canonicalVal hsymm heuclid w)

end
