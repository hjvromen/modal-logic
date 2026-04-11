import ModalLogic.Metatheory.MaximalHelpers
import ModalLogic.Syntax.SyntaxLemmas

/-!
# Canonical Models and Completeness Theorems (SIMPLIFIED)

This file constructs the canonical model and proves the strong completeness
theorems for modal logics K, T, S4, and S5.

**IMPROVEMENT**: This version uses derived lemmas from syntaxlemmas_improved.lean
to simplify proofs significantly, replacing complex raw axiom applications with
high-level derived rules.
-/

open Classical
--open Modal
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

------------------------------------------------------------------------------
-- § 1. Canonical Model Construction
------------------------------------------------------------------------------

/--
**Canonical Frame**: The frame where worlds are maximally AX-consistent sets
and the accessibility relation is defined via the necessity operator.
-/
def canonicalFrame (AX : Ctx) : Frame where
  states := World AX
  rel := fun w w' => ∀ φ, World.mem (□φ) w → World.mem φ w'

/--
**Canonical Valuation**: A proposition variable n holds at world w iff (var n) ∈ w.
-/
def canonicalVal : ℕ → World AX → Prop :=
  fun n w => World.mem (Form.var n) w

/- Note: A `canonicalModel` definition combining Frame + Valuation was removed
   because the `Model` structure is unused in this development. The canonical
   frame and valuation are used directly. -/

------------------------------------------------------------------------------
-- § 2. Truth Lemma
------------------------------------------------------------------------------

/--
**Truth Lemma**: A formula holds in a world of the canonical model iff
it's a member of that world's theory.
-/
theorem truthLemma (AX : Ctx) :
  ∀ (w : World AX) (φ : Form),
  forces (canonicalFrame AX) canonicalVal w φ ↔ World.mem φ w := by
  intro w φ
  induction φ generalizing w with
  | bot =>
    constructor
    · intro hforces
      simp [forces] at hforces
    · intro hmem
      have hcons : ax_consist AX w.toCtx := maximal_is_consistent w.toCtx w.isMaximal
      have : fin_ax_consist AX [Form.bot] :=
        hcons [Form.bot] (by intro ψ h; simp at h; rw [h]; exact hmem)
      simp [fin_ax_consist, fin_conj] at this
      -- SIMPLIFIED: Use cut and identity instead of raw axiom application
      exact this (cut (mp pl5 phi_and_true) identity)

  | var n =>
    constructor
    · intro hforces
      unfold forces canonicalVal at hforces
      exact hforces
    · intro hmem
      unfold forces canonicalVal
      exact hmem

  | and ψ χ ih_ψ ih_χ =>
    constructor
    · intro hforces
      simp [forces] at hforces
      obtain ⟨hψ_forces, hχ_forces⟩ := hforces
      rw [ih_ψ w] at hψ_forces
      rw [ih_χ w] at hχ_forces
      exact World.and_intro w hψ_forces hχ_forces
    · intro hmem
      simp [forces]
      have hψ_mem : World.mem ψ w := World.and_left w hmem
      have hχ_mem : World.mem χ w := World.and_right w hmem
      exact ⟨(ih_ψ w).mpr hψ_mem, (ih_χ w).mpr hχ_mem⟩

  | impl ψ χ ih_ψ ih_χ =>
    constructor
    · intro hforces
      simp [forces] at hforces
      apply World.imp_intro w
      intro hψ
      have hψ_forces : forces (canonicalFrame AX) canonicalVal w ψ :=
        (ih_ψ w).mpr hψ
      have hχ_forces := hforces hψ_forces
      exact (ih_χ w).mp hχ_forces
    · intro hmem
      simp [forces]
      intro hψ_forces
      rw [ih_ψ w] at hψ_forces
      rw [ih_χ w]
      exact World.mp w hmem hψ_forces

  | box ψ ih_ψ =>
    constructor
    · intro hforces
      unfold forces at hforces
      by_contra hnot
      have hneg_box : World.mem (∼(□ψ)) w := (World.not_mem_iff w (□ψ)).mp hnot
      have hdia_notψ : World.mem (∼(□(∼∼ψ))) w :=
        maximal_box_dn w.toCtx w.isMaximal ψ hneg_box

      let Δ_base : Ctx := {φ | World.mem (□φ) w} ∪ {∼ψ}

      have hcons_Δ : ax_consist AX Δ_base := by
        intro L hall
        by_contra hcontra
        rw [fin_ax_consist] at hcontra
        push_neg at hcontra

        obtain ⟨L', hL'_in_boxes, hprf⟩ := five_helper AX {φ | World.mem (□φ) w} (∼ψ) L Form.bot
          (fun φ hφ => by
            have : φ ∈ Δ_base := hall φ hφ
            simp [Δ_base, Set.mem_setOf_eq] at this
            cases this with
            | inl h => exact Or.inr h
            | inr h => exact Or.inl h)
          hcontra

        have hprf_nnψ : ProofK AX (fin_conj L' ⊃ (∼∼ψ)) := hprf
        have hall_boxed : ∀ φ ∈ L', World.mem (□φ) w := hL'_in_boxes

        let L'_boxed := L'.map (fun φ => □φ)
        have hall_boxed_in_w : ∀ χ ∈ L'_boxed, World.mem χ w := by
          intro χ hmem
          rw [List.mem_map] at hmem
          obtain ⟨φ, hφ_in, rfl⟩ := hmem
          exact hall_boxed φ hφ_in

        -- SIMPLIFIED: Use box_mono instead of raw kdist + nec
        have hbox_impl : ProofK AX (□(fin_conj L') ⊃ □(∼∼ψ)) :=
          box_mono hprf_nnψ

        have hboxn : ProofK AX (fin_conj L'_boxed ⊃ □(fin_conj L')) := fin_conj_boxn

        have hfinal : ProofK AX (fin_conj L'_boxed ⊃ □(∼∼ψ)) := cut hboxn hbox_impl

        have hbox_nnψ : World.mem (□(∼∼ψ)) w :=
          World.proves w hall_boxed_in_w hfinal

        have : ¬World.mem (□(∼∼ψ)) w := (World.not_mem_iff w (□(∼∼ψ))).mpr hdia_notψ
        exact this hbox_nnψ

      let w' := extendToMaximal Δ_base hcons_Δ

      have hnotψ_in_Δ : (∼ψ) ∈ w'.val :=
        w'.property.2 (Set.mem_union_right _ (Set.mem_singleton (∼ψ)))

      have : World.mem (∼ψ) ⟨w'.val, w'.property.1⟩ := hnotψ_in_Δ

      have hrel : ∀ φ, World.mem (□φ) w → World.mem φ ⟨w'.val, w'.property.1⟩ := by
        intro φ hbox
        apply w'.property.2
        left
        exact hbox

      have hψ_forces_w' : forces (canonicalFrame AX) canonicalVal ⟨w'.val, w'.property.1⟩ ψ :=
        hforces ⟨w'.val, w'.property.1⟩ hrel

      have hψ_in_w' : World.mem ψ ⟨w'.val, w'.property.1⟩ :=
        (ih_ψ ⟨w'.val, w'.property.1⟩).mp hψ_forces_w'

      have : ¬World.mem ψ ⟨w'.val, w'.property.1⟩ :=
        (World.not_mem_iff ⟨w'.val, w'.property.1⟩ ψ).mpr hnotψ_in_Δ
      exact this hψ_in_w'

    · intro hmem
      unfold forces
      intro w' hrel
      exact (ih_ψ w').mpr (hrel ψ hmem)

------------------------------------------------------------------------------
-- § 3. Completeness Theorems
------------------------------------------------------------------------------

/--
**Completeness for K**: If φ is valid in all frames, then φ is provable in K.
-/
theorem completeness_K (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop) (w : F.states), forces F v w φ) →
  ProofK ∅ φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist ∅ {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      have : ψ ∈ {∼φ} := hall ψ hmem
      exact Set.mem_singleton_iff.mp this
    have hneg_conj : ProofK ∅ (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK ∅ φ := fin_conj_repeat sem_consK hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World ∅ := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  have hrefute : ¬forces (canonicalFrame ∅) canonicalVal w φ := by
    intro hφ_forces
    have h_equiv := truthLemma ∅ w φ
    have hφ : World.mem φ w := h_equiv.mp hφ_forces
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame ∅) canonicalVal w)

/--
**Completeness for T**: If φ is valid in all reflexive frames,
then φ is provable in T.
-/
theorem completeness_T (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w, F.rel w w) → ∀ w, forces F v w φ) →
  ProofK TAxioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist TAxioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK TAxioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK TAxioms φ := fin_conj_repeat sem_consT hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World TAxioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  have hrefl : ∀ (w : World TAxioms), (canonicalFrame TAxioms).rel w w := by
    intro w'
    unfold canonicalFrame
    simp
    intro ψ hbox
    have hT_in_axioms : (□ψ ⊃ ψ) ∈ TAxioms := ⟨ψ, rfl⟩
    have hT_axiom : ProofK TAxioms (□ψ ⊃ ψ) := hyp hT_in_axioms
    have hT_imp_in_w' : World.mem (□ψ ⊃ ψ) w' := by
      apply World.proves w' (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        -- SIMPLIFIED: Use k_intro instead of mp pl1
        exact k_intro hT_axiom
    exact World.mp w' hT_imp_in_w' hbox

  have hrefute : ¬forces (canonicalFrame TAxioms) canonicalVal w φ := by
    rw [truthLemma TAxioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame TAxioms) canonicalVal hrefl w)

/--
**Completeness for S4**: If φ is valid in all reflexive and transitive frames,
then φ is provable in S4.
-/
theorem completeness_S4 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w, F.rel w w) →
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    ∀ w, forces F v w φ) →
  ProofK S4Axioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist S4Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK S4Axioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK S4Axioms φ := fin_conj_repeat sem_consS4 hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World S4Axioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  have hrefl : ∀ (w : World S4Axioms), (canonicalFrame S4Axioms).rel w w := by
    intro w'
    unfold canonicalFrame
    simp
    intro ψ hbox
    have hT_in_axioms : (□ψ ⊃ ψ) ∈ S4Axioms := by left; exact ⟨ψ, rfl⟩
    have hT_axiom : ProofK S4Axioms (□ψ ⊃ ψ) := hyp hT_in_axioms
    have hT_imp_in_w' : World.mem (□ψ ⊃ ψ) w' := by
      apply World.proves w' (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        -- SIMPLIFIED: Use k_intro instead of mp pl1
        exact k_intro hT_axiom
    exact World.mp w' hT_imp_in_w' hbox

  have htrans : ∀ (w₁ w₂ w₃ : World S4Axioms),
      (canonicalFrame S4Axioms).rel w₁ w₂ →
      (canonicalFrame S4Axioms).rel w₂ w₃ →
      (canonicalFrame S4Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox
    have h4_axiom_in : (□ψ ⊃ □□ψ) ∈ S4Axioms := by right; exact ⟨ψ, rfl⟩
    have h4_axiom : ProofK S4Axioms (□ψ ⊃ □□ψ) := hyp h4_axiom_in
    have h4_in_w₁ : World.mem (□ψ ⊃ □□ψ) w₁ := by
      apply World.proves w₁ (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        -- SIMPLIFIED: Use k_intro instead of mp pl1
        exact k_intro h4_axiom
    have hbox_box : World.mem (□□ψ) w₁ := World.mp w₁ h4_in_w₁ hbox
    have hbox_in_w₂ : World.mem (□ψ) w₂ := hrel₁₂ (□ψ) hbox_box
    exact hrel₂₃ ψ hbox_in_w₂

  have hrefute : ¬forces (canonicalFrame S4Axioms) canonicalVal w φ := by
    rw [truthLemma S4Axioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame S4Axioms) canonicalVal hrefl htrans w)

/--
**Euclidean Duality Helper Lemma**:
From the S5 axiom (◇¬φ ⊃ □◇¬φ), derive (◇□φ ⊃ □φ).

This lemma establishes that euclidean accessibility implies the S5 characteristic axiom.

**SIGNIFICANTLY SIMPLIFIED**: The original proof used raw PL1, PL2, PL3 axioms extensively
with nested mp calls. This version uses high-level lemmas from syntaxlemmas_improved.lean:
- `box_mono` for modal reasoning
- `cut` for implication composition
- `contrapos` for contraposition
- `dual_equiv1` and `dual_equiv2` for box-diamond duality
- `dne` and `dni` for double negation

-/
lemma euclid_dual {φ : Form} :
  ProofK S5Axioms ((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (◇(□φ) ⊃ □φ)) := by
  /- High-level proof strategy:
     Assume the hypothesis H: (◇¬φ ⊃ □◇¬φ) and derive (◇□φ ⊃ □φ)
     1. Show (◇¬φ ⊃ ¬□φ) using duality
     2. From H and Step 1, derive (¬□φ ⊃ □¬□φ)
     3. Use duality to transform (□¬□φ) into (¬◇□φ)
     4. Apply contraposition to get (◇□φ ⊃ □φ)
     Then package this as an implication from the hypothesis.
  -/

  -- We need to prove: H ⊃ Goal, so we'll work with H as a hypothesis
  -- and then use implication introduction (which we need to do manually in Hilbert style)

  -- Step 1: Prove (◇¬φ ⊃ ¬□φ) as a theorem (without the S5 axiom)
  have dia_to_notbox_base : ProofK S5Axioms ((◇(∼φ)) ⊃ (∼(□φ))) := by
    -- ◇¬φ ↔ ¬□¬¬φ (by dual_equiv2)
    have d2 : ProofK S5Axioms (◇(∼φ) ⇔ ∼(□(∼(∼φ)))) :=
      dual_equiv2 (φ := ∼φ)
    -- ◇¬φ ⊃ ¬□¬¬φ
    have dia_to_notboxdn : ProofK S5Axioms ((◇(∼φ)) ⊃ (∼(□(∼(∼φ))))) :=
      mp pl5 d2
    -- □φ ⊃ □¬¬φ (by box_mono dni)
    have box_dn_i : ProofK S5Axioms (□φ ⊃ □(∼(∼φ))) :=
      box_mono (dni (φ := φ))
    -- By contraposition: ¬□¬¬φ ⊃ ¬□φ
    have notboxdn_to_notbox : ProofK S5Axioms (∼(□(∼(∼φ))) ⊃ ∼(□φ)) :=
      contrapos.mpr box_dn_i
    -- Compose to get: ◇¬φ ⊃ ¬□φ
    exact cut dia_to_notboxdn notboxdn_to_notbox

  -- Step 2: We can necessitate this and use K to get: □◇¬φ ⊃ □¬□φ
  have boxdia_to_boxnotbox : ProofK S5Axioms (□(◇(∼φ)) ⊃ □(∼(□φ))) :=
    box_mono dia_to_notbox_base

  -- Step 3: Apply duality: □¬□φ ⊃ ¬◇□φ
  -- dual_equiv1 states: □ψ ↔ ¬◇¬ψ
  -- We need: □¬□φ ↔ ¬◇¬(¬□φ) = ¬◇□φ
  -- So instantiate with ψ := ¬□φ
  have d1 : ProofK S5Axioms (□(∼(□φ)) ⇔ ∼(◇(∼(∼(□φ))))) :=
    dual_equiv1 (φ := ∼(□φ))
  -- Simplify: ¬¬□φ = □φ using double negation
  -- We have: □¬□φ ↔ ¬◇¬¬□φ
  -- We need: □¬□φ ↔ ¬◇□φ, so we need to eliminate the double negation inside ◇

  -- Let's use: ¬◇¬¬□φ = ¬◇□φ by double negation elimination
  -- First direction: □¬□φ ⊃ ¬◇¬¬□φ
  have boxnotbox_to_notdiadn : ProofK S5Axioms (□(∼(□φ)) ⊃ ∼(◇(∼(∼(□φ))))) :=
    mp pl5 d1

  -- Now we need: ¬◇¬¬□φ ⊃ ¬◇□φ
  -- This is: (◇□φ ⊃ ◇¬¬□φ) contraposed
  -- And ◇□φ ⊃ ◇¬¬□φ follows from □φ ⊃ ¬¬□φ (which is dni) lifted to diamond

  -- We need ¬◇¬¬□φ ⊃ ¬◇□φ, equivalently ◇□φ ⊃ ◇¬¬□φ by contraposition.
  -- This follows from diamond monotonicity with double negation introduction.

  -- First prove diamond is monotonic
  -- If (φ ⊃ ψ) then (◇φ ⊃ ◇ψ)
  -- ◇φ = ¬□¬φ, ◇ψ = ¬□¬ψ
  -- If (φ ⊃ ψ) then (¬ψ ⊃ ¬φ) by contraposition
  -- If (¬ψ ⊃ ¬φ) then (□¬ψ ⊃ □¬φ) by box_mono
  -- If (□¬ψ ⊃ □¬φ) then (¬□¬φ ⊃ ¬□¬ψ) by contraposition
  -- So: ◇φ ⊃ ◇ψ

  have dia_dni : ProofK S5Axioms (◇(□φ) ⊃ ◇(∼(∼(□φ)))) := by
    have dni_box : ProofK S5Axioms (□φ ⊃ ∼(∼(□φ))) := dni (φ := □φ)
    have contra_dni : ProofK S5Axioms (∼(∼(∼(□φ))) ⊃ ∼(□φ)) := contrapos.mpr dni_box
    have box_contra : ProofK S5Axioms (□(∼(∼(∼(□φ)))) ⊃ □(∼(□φ))) := box_mono contra_dni
    exact contrapos.mpr box_contra

  have notdiadn_to_notdia : ProofK S5Axioms (∼(◇(∼(∼(□φ)))) ⊃ ∼(◇(□φ))) :=
    contrapos.mpr dia_dni

  have boxnotbox_to_notdia : ProofK S5Axioms (□(∼(□φ)) ⊃ ∼(◇(□φ))) :=
    cut boxnotbox_to_notdiadn notdiadn_to_notdia

  -- Step 4: Compose to get: □◇¬φ ⊃ ¬◇□φ
  have boxdia_to_notdia : ProofK S5Axioms (□(◇(∼φ)) ⊃ ∼(◇(□φ))) :=
    cut boxdia_to_boxnotbox boxnotbox_to_notdia

  -- Step 5: Apply contraposition to get: ◇□φ ⊃ ¬□◇¬φ
  -- We have: (□◇¬φ ⊃ ¬◇□φ)
  -- We want: (◇□φ ⊃ ¬□◇¬φ)
  -- contrapos_mp: (A ⊃ B) ⊃ (¬B ⊃ ¬A)
  -- Instantiate with A = □◇¬φ, B = ¬◇□φ
  -- This gives: (□◇¬φ ⊃ ¬◇□φ) ⊃ (¬¬◇□φ ⊃ ¬□◇¬φ)

  have contrapos_applied : ProofK S5Axioms
      ((□(◇(∼φ)) ⊃ ∼(◇(□φ))) ⊃ (∼(∼(◇(□φ))) ⊃ ∼(□(◇(∼φ))))) :=
    contrapos_mp (φ := □(◇(∼φ))) (ψ := ∼(◇(□φ)))

  have dia_to_notboxdia_dn : ProofK S5Axioms (∼(∼(◇(□φ))) ⊃ ∼(□(◇(∼φ)))) :=
    mp contrapos_applied boxdia_to_notdia

  -- Simplify: ¬¬◇□φ to ◇□φ using dni on the left
  have dia_to_notboxdia : ProofK S5Axioms (◇(□φ) ⊃ ∼(□(◇(∼φ)))) := by
    have dni_dia : ProofK S5Axioms (◇(□φ) ⊃ ∼(∼(◇(□φ)))) := dni (φ := ◇(□φ))
    exact cut dni_dia dia_to_notboxdia_dn

  -- Step 6: Now we need to relate ¬□◇¬φ back to □φ using the S5 axiom
  -- The S5 axiom is: ◇¬φ ⊃ □◇¬φ
  -- Contraposing: ¬□◇¬φ ⊃ ¬◇¬φ
  -- And ¬◇¬φ = □¬¬φ (by duality)
  -- And □¬¬φ ⊃ □φ (by box_mono dne)

  -- First, let's prove: ¬□◇¬φ ⊃ □φ assuming (◇¬φ ⊃ □◇¬φ)
  -- This is where we need to use the hypothesis

  -- In the extended context with (◇¬φ ⊃ □◇¬φ), we can derive (◇□φ ⊃ □φ)
  -- Let's build this step by step

  -- We need: ¬◇¬φ ↔ □¬¬φ
  -- Strategy: Use dual_equiv2 and manipulate it
  -- dual_equiv2: ◇ψ ↔ ¬□¬ψ
  -- With ψ = ¬φ: ◇¬φ ↔ ¬□¬¬φ
  -- Contrapose/negate: ¬◇¬φ ↔ ¬¬□¬¬φ ↔ □¬¬φ (by DNE)
  have notdia_to_boxdn_mp : ProofK S5Axioms (∼(◇(∼φ)) ⊃ □(∼(∼φ))) := by
    -- From dual_equiv2, we know: ◇¬φ ↔ ¬□¬¬φ
    have d2 : ProofK S5Axioms (◇(∼φ) ⇔ ∼(□(∼(∼φ)))) :=
      dual_equiv2 (φ := ∼φ)
    -- Extract: ¬□¬¬φ ⊃ ◇¬φ
    have h1 : ProofK S5Axioms (∼(□(∼(∼φ))) ⊃ ◇(∼φ)) :=
      mp pl6 d2
    -- Contrapose to get: ¬◇¬φ ⊃ ¬¬□¬¬φ
    have h2 : ProofK S5Axioms (∼(◇(∼φ)) ⊃ ∼∼(□(∼(∼φ)))) :=
      contrapos.mpr h1
    -- Apply DNE: ¬◇¬φ ⊃ □¬¬φ
    exact cut h2 (dne (φ := □(∼(∼φ))))

  -- □¬¬φ ⊃ □φ (by box_mono dne)
  have boxdn_to_box : ProofK S5Axioms (□(∼(∼φ)) ⊃ □φ) :=
    box_mono (dne (φ := φ))

  -- Compose: ¬◇¬φ ⊃ □φ
  have notdia_to_box : ProofK S5Axioms (∼(◇(∼φ)) ⊃ □φ) :=
    cut notdia_to_boxdn_mp boxdn_to_box

  -- Now we need to connect this with our earlier result
  -- We have: ◇□φ ⊃ ¬□◇¬φ
  -- We want to add: (◇¬φ ⊃ □◇¬φ) as hypothesis and derive: ◇□φ ⊃ □φ

  -- Key insight: If (◇¬φ ⊃ □◇¬φ), then by contraposition: ¬□◇¬φ ⊃ ¬◇¬φ
  -- So: ◇□φ ⊃ ¬□◇¬φ ⊃ ¬◇¬φ ⊃ □φ

  -- Let's construct this carefully
  -- We need: ((◇¬φ ⊃ □◇¬φ) ⊃ (◇□φ ⊃ □φ))

  -- Step A: (◇¬φ ⊃ □◇¬φ) ⊃ (¬□◇¬φ ⊃ ¬◇¬φ) by contraposition
  have step_a : ProofK S5Axioms
      ((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (∼(□(◇(∼φ))) ⊃ ∼(◇(∼φ)))) :=
    contrapos_mp

  -- Step B: (¬◇¬φ ⊃ □φ) - we have this as notdia_to_box

  -- Step C: Compose (¬□◇¬φ ⊃ ¬◇¬φ) and (¬◇¬φ ⊃ □φ) to get (¬□◇¬φ ⊃ □φ)
  -- This gives us: (◇¬φ ⊃ □◇¬φ) ⊃ (¬□◇¬φ ⊃ □φ)
  -- Using hypothetical syllogism / composition

  -- We need: ((A ⊃ (B ⊃ C)) ⊃ ((A ⊃ D) ⊃ (A ⊃ E))) but actually simpler:
  -- From (H ⊃ (P ⊃ Q)) and (Q ⊃ R), derive (H ⊃ (P ⊃ R))

  -- Let's use cut1: (θ ⊃ (φ ⊃ ψ)) → (ψ ⊃ χ) → (θ ⊃ (φ ⊃ χ))
  have step_bc : ProofK S5Axioms
      ((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (∼(□(◇(∼φ))) ⊃ □φ)) :=
    cut1 step_a notdia_to_box

  -- Step D: We have (◇□φ ⊃ ¬□◇¬φ) as dia_to_notboxdia

  -- Step E: Compose to get: (◇¬φ ⊃ □◇¬φ) ⊃ (◇□φ ⊃ □φ)
  -- We need to combine:
  --   (◇¬φ ⊃ □◇¬φ) ⊃ (¬□◇¬φ ⊃ □φ)  [step_bc]
  --   (◇□φ ⊃ ¬□◇¬φ)                   [dia_to_notboxdia]
  -- To get:
  --   (◇¬φ ⊃ □◇¬φ) ⊃ (◇□φ ⊃ □φ)

  -- Using hs2: (φ ⊃ ψ) ⊃ ((ψ ⊃ χ) ⊃ (φ ⊃ χ))
  -- Instantiate with φ := ◇□φ, ψ := ¬□◇¬φ, χ := □φ
  -- This gives: (◇□φ ⊃ ¬□◇¬φ) ⊃ ((¬□◇¬φ ⊃ □φ) ⊃ (◇□φ ⊃ □φ))
  have hs2_inst : ProofK S5Axioms
      ((◇(□φ) ⊃ ∼(□(◇(∼φ)))) ⊃
       ((∼(□(◇(∼φ))) ⊃ □φ) ⊃ (◇(□φ) ⊃ □φ))) :=
    hs2

  -- Apply dia_to_notboxdia to get: (¬□◇¬φ ⊃ □φ) ⊃ (◇□φ ⊃ □φ)
  have middle : ProofK S5Axioms ((∼(□(◇(∼φ))) ⊃ □φ) ⊃ (◇(□φ) ⊃ □φ)) :=
    mp hs2_inst dia_to_notboxdia

  -- Now use hs2 again to combine with step_bc
  -- We have:
  --   (◇¬φ ⊃ □◇¬φ) ⊃ (¬□◇¬φ ⊃ □φ)       [step_bc]
  --   (¬□◇¬φ ⊃ □φ) ⊃ (◇□φ ⊃ □φ)         [middle]
  -- We want:
  --   (◇¬φ ⊃ □◇¬φ) ⊃ (◇□φ ⊃ □φ)

  -- Using hs1: (ψ ⊃ χ) ⊃ ((φ ⊃ ψ) ⊃ (φ ⊃ χ))
  -- Instantiate with φ := (◇¬φ ⊃ □◇¬φ), ψ := (¬□◇¬φ ⊃ □φ), χ := (◇□φ ⊃ □φ)
  have hs1_inst : ProofK S5Axioms
      (((∼(□(◇(∼φ))) ⊃ □φ) ⊃ (◇(□φ) ⊃ □φ)) ⊃
       (((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (∼(□(◇(∼φ))) ⊃ □φ)) ⊃
        ((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (◇(□φ) ⊃ □φ)))) :=
    hs1

  have almost : ProofK S5Axioms
      (((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (∼(□(◇(∼φ))) ⊃ □φ)) ⊃
       ((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (◇(□φ) ⊃ □φ))) :=
    mp hs1_inst middle

  exact mp almost step_bc

/--
**Completeness for S5**: If φ is valid in all equivalence frames,
then φ is provable in S5.
-/
theorem completeness_S5 (φ : Form) :
  (∀ (F : Frame.{0}) (v : ℕ → F.states → Prop),
    (∀ w, F.rel w w) →
    (∀ w₁ w₂, F.rel w₁ w₂ → F.rel w₂ w₁) →
    (∀ w₁ w₂ w₃, F.rel w₁ w₂ → F.rel w₂ w₃ → F.rel w₁ w₃) →
    ∀ w, forces F v w φ) →
  ProofK S5Axioms φ := by
  intro hvalid
  by_contra hnot_prf

  have hcons : ax_consist S5Axioms {∼φ} := by
    intro L hall
    by_contra hcontra
    rw [fin_ax_consist] at hcontra
    push_neg at hcontra
    have hL_subset : ∀ ψ ∈ L, ψ = ∼φ := by
      intro ψ hmem
      exact Set.mem_singleton_iff.mp (hall ψ hmem)
    have hneg_conj : ProofK S5Axioms (∼(fin_conj L)) := hcontra
    have hprf_φ : ProofK S5Axioms φ := fin_conj_repeat sem_consS5 hL_subset hneg_conj
    exact hnot_prf hprf_φ

  let w_subtype := extendToMaximal {∼φ} hcons
  let w : World S5Axioms := ⟨w_subtype.val, w_subtype.property.1⟩

  have hneg_φ : World.mem (∼φ) w :=
    w_subtype.property.2 (Set.mem_singleton (∼φ))

  have hrefl : ∀ (w : World S5Axioms), (canonicalFrame S5Axioms).rel w w := by
    intro w'
    unfold canonicalFrame
    simp
    intro ψ hbox
    have hT_in_axioms : (□ψ ⊃ ψ) ∈ S5Axioms := by left; exact ⟨ψ, rfl⟩
    have hT_axiom : ProofK S5Axioms (□ψ ⊃ ψ) := hyp hT_in_axioms
    have hT_imp_in_w' : World.mem (□ψ ⊃ ψ) w' := by
      apply World.proves w' (L := [])
      · intro χ hmem; cases hmem
      · simp [fin_conj]
        -- SIMPLIFIED: Use k_intro instead of mp pl1
        exact k_intro hT_axiom
    exact World.mp w' hT_imp_in_w' hbox

  have heucl : ∀ (w₁ w₂ w₃ : World S5Axioms),
      (canonicalFrame S5Axioms).rel w₁ w₂ →
      (canonicalFrame S5Axioms).rel w₁ w₃ →
      (canonicalFrame S5Axioms).rel w₂ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₁₃
    unfold canonicalFrame at *
    simp at *
    intro ψ hbox_ψ

    have hdia_box : World.mem (◇(□ψ)) w₁ := by
      by_contra hnot_dia
      have hneg_dia : World.mem (∼(◇(□ψ))) w₁ :=
        (World.not_mem_iff w₁ (◇(□ψ))).mp hnot_dia
      have hbox_not_box : World.mem (□(∼(□ψ))) w₁ :=
        (World.double_neg w₁ (□(∼(□ψ)))).mpr hneg_dia
      have hnot_box : World.mem (∼(□ψ)) w₂ := hrel₁₂ (∼(□ψ)) hbox_not_box
      have : ¬World.mem (□ψ) w₂ := (World.not_mem_iff w₂ (□ψ)).mpr hnot_box
      exact this hbox_ψ

    have hbox_ψ_in_w₁ : World.mem (□ψ) w₁ := by
      have h5_axiom : (◇(∼ψ) ⊃ □◇(∼ψ)) ∈ S5Axioms := by
        right
        exact ⟨∼ψ, rfl⟩
      have h5_prf : ProofK S5Axioms (◇(∼ψ) ⊃ □◇(∼ψ)) := hyp h5_axiom
      have h_dual : ProofK S5Axioms (◇(□ψ) ⊃ □ψ) := mp euclid_dual h5_prf
      have h_dual_in : World.mem (◇(□ψ) ⊃ □ψ) w₁ := by
        apply World.proves w₁ (L := [])
        · intro χ hmem; cases hmem
        · simp [fin_conj]
          -- SIMPLIFIED: Use k_intro instead of mp pl1
          exact k_intro h_dual
      exact World.mp w₁ h_dual_in hdia_box

    exact hrel₁₃ ψ hbox_ψ_in_w₁

  have hsymm : ∀ (w₁ w₂ : World S5Axioms),
      (canonicalFrame S5Axioms).rel w₁ w₂ →
      (canonicalFrame S5Axioms).rel w₂ w₁ := by
    intro w₁ w₂ hrel₁₂
    exact heucl w₁ w₂ w₁ hrel₁₂ (hrefl w₁)

  have htrans : ∀ (w₁ w₂ w₃ : World S5Axioms),
      (canonicalFrame S5Axioms).rel w₁ w₂ →
      (canonicalFrame S5Axioms).rel w₂ w₃ →
      (canonicalFrame S5Axioms).rel w₁ w₃ := by
    intro w₁ w₂ w₃ hrel₁₂ hrel₂₃
    have : (canonicalFrame S5Axioms).rel w₂ w₁ := hsymm w₁ w₂ hrel₁₂
    exact heucl w₂ w₁ w₃ this hrel₂₃

  have hrefute : ¬forces (canonicalFrame S5Axioms) canonicalVal w φ := by
    rw [truthLemma S5Axioms w]
    intro hφ
    have hφ_notin : ¬World.mem φ w := (World.not_mem_iff w φ).mpr hneg_φ
    exact hφ_notin hφ

  exact hrefute (hvalid (canonicalFrame S5Axioms) canonicalVal hrefl hsymm htrans w)

end


/-!
Helper lemma name used elsewhere in the project. It is definitionally
the same statement as `euclid_dual`.
-/
lemma euclid_helper {φ : Form} :
  ProofK S5Axioms ((◇(∼φ) ⊃ □(◇(∼φ))) ⊃ (◇(□φ) ⊃ □φ)) :=
  euclid_dual
