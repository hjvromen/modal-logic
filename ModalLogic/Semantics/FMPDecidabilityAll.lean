/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Finite Model Property and Decidability for More Modal Logics

This file extends the FMP and decidability results to 7 additional modal logics:
**K4** (transitive), **S4** (reflexive-transitive), **KD4** (serial-transitive),
**KTB** (reflexive-symmetric), **KDB** (serial-symmetric), **KB4** (symmetric-transitive),
and **KB5** (symmetric-Euclidean).

## Method

Two techniques are used:

### 1. Smallest filtration (for KTB, KDB)
For logics whose frame conditions are all preserved by the smallest filtration
(reflexivity, symmetry, seriality), FMP follows directly from the existing
filtration infrastructure.

### 2. Transitive closure filtration (for K4, S4, KD4, KB4, KB5)
For logics involving transitivity, the smallest filtration does NOT preserve
transitivity. Instead, we take the **transitive closure** of the smallest
filtration relation. This produces a valid filtration (the filtration lemma
still holds) provided the original frame is transitive, and the resulting
relation is transitive by construction.

Key insight: if `forces(x, □ψ)` and the original frame is transitive, then
`□ψ` is preserved along any chain of smallest-filtration steps, allowing the
filtration lemma to be proven by induction on the `TransGen` chain.

The transitive closure also preserves symmetry (TransGen of a symmetric
relation is symmetric), so KB4 follows directly.

For KB5: symmetric + Euclidean implies transitive, so the transitive closure
technique applies. Conversely, symmetric + transitive implies Euclidean, so
the filtration result is also symmetric + Euclidean.

## Main Results

- `fmp_K4`, `fmp_S4`, `fmp_KD4`, `fmp_KTB`, `fmp_KDB`, `fmp_KB4`, `fmp_KB5`
- `decidable_k4Valid`, `decidable_s4Valid`, `decidable_kd4Valid`,
  `decidable_ktbValid`, `decidable_kdbValid`, `decidable_kb4Valid`,
  `decidable_kb5Valid`

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §2.3 (filtration)
- Chellas, *Modal Logic: An Introduction*, Ch. 5 (filtration and FMP)
-/

import ModalLogic.Semantics.DecidabilityMore

namespace Modal
open Modal
open BasicModal

/-!
## § 1. Transitive Closure Filtration

The **transitive closure filtration** has the same states as the smallest
filtration (equivalence classes under subformula equivalence), but uses
`Relation.TransGen` of the smallest filtration relation. This ensures
transitivity by construction.
-/

/-- The transitive closure filtration frame: same equivalence classes as the
smallest filtration, but with `TransGen` of the filtration relation.
This is transitive by construction. -/
noncomputable def transFiltrationFrame (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Frame where
  states := (filtrationFrame F v φ).states
  rel := Relation.TransGen (filtrationFrame F v φ).rel

/-- The transitive closure filtration is finite (same states as smallest filtration). -/
noncomputable instance transFiltration_finite (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Finite (transFiltrationFrame F v φ).states :=
  filtration_finite F v φ

/-- The transitive closure filtration has the same cardinality bound. -/
lemma transFiltrationFrame_card_le (F : Frame) (v : Nat → F.states → Prop) (φ : Form) :
    @Fintype.card (transFiltrationFrame F v φ).states (Fintype.ofFinite _) ≤
      2 ^ (subformulas φ).length :=
  filtrationFrame_card_le F v φ

/-!
## § 2. Key Lemma: Box Forces Along TransGen Chains

In a transitive frame, if `forces(x, □ψ)` holds and there is a TransGen chain
from `⟦x⟧` to some quotient element `q`, then both `ψ` and `□ψ` hold at `q.out`.

This is the core argument enabling the transitive closure filtration lemma.
-/

/-
Helper: the smallest filtration relation at a single step preserves box forces
when the frame is transitive.
-/
lemma forces_box_single_step (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hTrans : Transitive F.rel)
    (ψ : Form) (hψ_box : Form.box ψ ∈ subformulas φ)
    (q₁ q₂ : (filtrationFrame F v φ).states)
    (hrel : (filtrationFrame F v φ).rel q₁ q₂)
    (hbox : forces F v q₁.out (Form.box ψ)) :
    forces F v q₂.out ψ ∧ forces F v q₂.out (Form.box ψ) := by
      -- By definition of filtration, there exist x' and y' such that x' is equivalent to q₁.out, y' is equivalent to q₂.out, and F.rel x' y'.
      obtain ⟨x', y', hx', hy', hxy'⟩ : ∃ x' y' : F.states, subfmlEquiv F v φ (Quotient.out q₁) x' ∧ subfmlEquiv F v φ (Quotient.out q₂) y' ∧ F.rel x' y' := by
        convert hrel using 1;
        unfold filtrationFrame;
        simp +decide ;
        rw [ ← Quotient.out_eq q₁, ← Quotient.out_eq q₂ ];
        erw [ Quotient.lift₂_mk ];
        simp +decide [ subfmlEquiv ];
      have h_forces_x' : forces F v x' (Form.box ψ) := by
        exact hx' _ hψ_box |>.1 hbox
      have h_forces_y' : forces F v y' ψ := by
        exact h_forces_x' y' hxy'
      have h_forces_y'_box : forces F v y' (Form.box ψ) := by
        exact fun z hz => h_forces_x' _ ( hTrans hxy' hz );
      exact ⟨ hy' ψ ( by exact box_subformula_imp_subformula hψ_box ) |>.2 h_forces_y', hy' ( Form.box ψ ) ( by exact Multiset.mem_coe.mp hψ_box ) |>.2 h_forces_y'_box ⟩

/-
In a transitive frame, box forces are preserved along TransGen chains of the
smallest filtration. If `forces(q₁.out, □ψ)` and `TransGen R q₁ q₂` and
`□ψ ∈ Sub(φ)`, then `forces(q₂.out, ψ)` and `forces(q₂.out, □ψ)`.
-/
lemma forces_box_along_transGen (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hTrans : Transitive F.rel)
    (ψ : Form) (hψ_box : Form.box ψ ∈ subformulas φ)
    (q₁ q₂ : (filtrationFrame F v φ).states)
    (hchain : Relation.TransGen (filtrationFrame F v φ).rel q₁ q₂)
    (hbox : forces F v q₁.out (Form.box ψ)) :
    forces F v q₂.out ψ ∧ forces F v q₂.out (Form.box ψ) := by
      induction' hchain with q₁ q₂ hchain ih;
      · (expose_names; exact forces_box_single_step F v φ hTrans ψ hψ_box q₁_1 q₁ q₂ hbox);
      · apply forces_box_single_step F v φ hTrans ψ hψ_box hchain ih ‹_› (by tauto)

/-!
## § 3. Filtration Lemma for Transitive Frames

The filtration lemma holds for the transitive closure of the smallest filtration
when the original frame is transitive. The proof is by induction on the formula:
- For the box case (→): use `forces_box_along_transGen`
- For the box case (←): use `TransGen.single` (since `R(x,y)` implies the
  smallest filtration has `⟦x⟧ R ⟦y⟧`)
-/

/-
Quotient representatives preserve forces for subformulas.
-/
lemma forces_out_iff (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x : F.states) (ψ : Form) (hψ : ψ ∈ subformulas φ) :
    forces F v x ψ ↔ forces F v (Quotient.mk (subfmlSetoid F v φ) x).out ψ := by
      convert filtration_lemma F v φ x ψ hψ using 1;
      rw [ filtration_lemma ];
      rw [ Quotient.out_eq ];
      assumption

/-
**Filtration lemma for transitive closure filtration**: For any subformula ψ of φ,
truth in the original model is equivalent to truth in the transitive closure
filtration model, provided the original frame is transitive.
-/
theorem transFiltration_lemma (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hTrans : Transitive F.rel)
    (x : F.states) (ψ : Form) (hψ : ψ ∈ subformulas φ) :
    forces F v x ψ ↔
      forces (transFiltrationFrame F v φ) (filtrationVal F v φ)
        (Quotient.mk (subfmlSetoid F v φ) x) ψ := by
          induction' ψ with ψ₁ ψ₂ hψ₁ hψ₂ generalizing x;
          · aesop;
          · unfold transFiltrationFrame filtrationVal;
            unfold forces; aesop;
          · have := and_subformula_left hψ; have := and_subformula_right hψ; aesop;
          · grind +suggestions;
          · constructor <;> intro h;
            · have h_trans : ∀ q : (filtrationFrame F v φ).states, Relation.TransGen (filtrationFrame F v φ).rel ⟦x⟧ q → forces F v q.out ‹_› := by
                intros q hq
                apply (forces_box_along_transGen F v φ hTrans _ hψ _ _ hq (by
                rw [ ← forces_out_iff F v φ x _ hψ ] ; assumption)).left;
              exact fun q hq => by simpa using h_trans q hq |> fun h => by simpa using ‹∀ x : F.states, _ ∈ subformulas φ → ( forces F v x _ ↔ forces ( transFiltrationFrame F v φ ) ( filtrationVal F v φ ) ⟦x⟧ _ ) › _ ( box_subformula_imp_subformula hψ ) |>.1 h;
            · intro y hy;
              have := h (⟦y⟧) (Relation.TransGen.single (by
              exact ⟨ x, y, subfmlEquiv_refl _, subfmlEquiv_refl _, hy ⟩));
              rename_i h₁ h₂;
              exact h₂ y ( box_subformula_imp_subformula hψ ) |>.2 this

/-!
## § 4. Preservation of Frame Properties by TransGen

The transitive closure of the smallest filtration preserves:
- **Transitivity**: by construction (`TransGen` is transitive)
- **Reflexivity**: if the smallest filtration is reflexive, so is `TransGen`
- **Seriality**: if the smallest filtration is serial, so is `TransGen`
- **Symmetry**: `TransGen` of a symmetric relation is symmetric
-/

/-- TransGen is transitive (standard library result). -/
lemma transGen_transitive {α : Type*} {R : α → α → Prop} :
    Transitive (Relation.TransGen R) :=
  fun _ _ _ h1 h2 => h1.trans h2

/-- TransGen preserves reflexivity (via `TransGen.single`). -/
lemma transGen_preserves_reflexivity {α : Type*} {R : α → α → Prop}
    (hRef : Reflexive R) : Reflexive (Relation.TransGen R) :=
  fun x => Relation.TransGen.single (hRef x)

/-- TransGen preserves seriality. -/
lemma transGen_preserves_seriality {α : Type*} {R : α → α → Prop}
    (hSer : ∀ x, ∃ y, R x y) : ∀ x, ∃ y, Relation.TransGen R x y :=
  fun x => let ⟨y, hy⟩ := hSer x; ⟨y, Relation.TransGen.single hy⟩

/-
TransGen of a symmetric relation is symmetric.
-/
lemma transGen_preserves_symmetry {α : Type*} {R : α → α → Prop}
    (hSymm : Symmetric R) : Symmetric (Relation.TransGen R) := by
      exact Relation.TransGen.symmetric hSymm

/-!
## § 5. Frame Property Consequences
-/

/-- Symmetric + Euclidean implies Transitive. -/
lemma symm_euclid_imp_trans {α : Type*} {R : α → α → Prop}
    (hSymm : Symmetric R) (hEuclid : Euclidean R) : Transitive R :=
  fun _ _ _ hxy hyz => hEuclid (hSymm hxy) hyz

/-- Symmetric + Transitive implies Euclidean. -/
lemma symm_trans_imp_euclid {α : Type*} {R : α → α → Prop}
    (hSymm : Symmetric R) (hTrans : Transitive R) : Euclidean R :=
  fun _ _ _ hxy hxz => hTrans (hSymm hxy) hxz

/-!
## § 6. Combined Preservation Results for the Transitive Closure Filtration
-/

/-- The transitive closure filtration of a transitive frame is transitive. -/
theorem transFiltration_transitive (F : Frame) (v : Nat → F.states → Prop) (φ : Form) :
    Transitive (transFiltrationFrame F v φ).rel :=
  transGen_transitive

/-- The transitive closure filtration of a reflexive frame is reflexive
(inherits from smallest filtration's reflexivity). -/
theorem transFiltration_reflexive (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hRef : Reflexive F.rel) :
    Reflexive (transFiltrationFrame F v φ).rel :=
  transGen_preserves_reflexivity (filtration_preserves_reflexivity F v φ hRef)

/-- The transitive closure filtration of a serial frame is serial. -/
theorem transFiltration_serial (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hSer : BasicModal.Serial F.rel) :
    BasicModal.Serial (transFiltrationFrame F v φ).rel :=
  transGen_preserves_seriality (filtration_preserves_seriality F v φ hSer)

/-- The transitive closure filtration of a symmetric frame is symmetric. -/
theorem transFiltration_symmetric (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hSymm : Symmetric F.rel) :
    Symmetric (transFiltrationFrame F v φ).rel :=
  transGen_preserves_symmetry (filtration_preserves_symmetry F v φ hSymm)

/-!
## § 7. Validity and Satisfiability Definitions
-/

/-- **K4-validity**: φ is valid in all transitive frames. -/
def k4Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Transitive F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **S4-validity**: φ is valid in all reflexive-transitive frames. -/
def s4Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Reflexive F.rel → Transitive F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KD4-validity**: φ is valid in all serial-transitive frames. -/
def kd4Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), BasicModal.Serial F.rel → Transitive F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KTB-validity**: φ is valid in all reflexive-symmetric frames. -/
def ktbValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Reflexive F.rel → Symmetric F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KDB-validity**: φ is valid in all serial-symmetric frames. -/
def kdbValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), BasicModal.Serial F.rel → Symmetric F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KB4-validity**: φ is valid in all symmetric-transitive frames. -/
def kb4Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Symmetric F.rel → Transitive F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KB5-validity**: φ is valid in all symmetric-Euclidean frames. -/
def kb5Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Symmetric F.rel → Euclidean F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 8. Satisfiability in Frame Classes
-/

def transSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def refTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Reflexive F.rel ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finRefTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Reflexive F.rel ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def serialTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), BasicModal.Serial F.rel ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finSerialTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ BasicModal.Serial F.rel ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def refSymmSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Reflexive F.rel ∧ Symmetric F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finRefSymmSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Reflexive F.rel ∧ Symmetric F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def serialSymmSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), BasicModal.Serial F.rel ∧ Symmetric F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finSerialSymmSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ BasicModal.Serial F.rel ∧ Symmetric F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def symmTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Symmetric F.rel ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finSymmTransSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Symmetric F.rel ∧ Transitive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def symmEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Symmetric F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finSymmEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Symmetric F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 9. FMP Theorems (Smallest Filtration: KTB, KDB)
-/

/-- **FMP for KTB**: Satisfiability in reflexive-symmetric frames implies
finite satisfiability in reflexive-symmetric frames. Uses the smallest
filtration, which preserves both reflexivity and symmetry. -/
theorem fmp_KTB (φ : Form) : refSymmSatisfiable φ → finRefSymmSatisfiable φ := by
  rintro ⟨F, hRef, hSymm, v, w, hw⟩
  exact ⟨filtrationFrame F v φ, inferInstance,
    filtration_preserves_reflexivity F v φ hRef,
    filtration_preserves_symmetry F v φ hSymm,
    filtrationVal F v φ, ⟦w⟧,
    (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for KDB**: Satisfiability in serial-symmetric frames implies
finite satisfiability in serial-symmetric frames. -/
theorem fmp_KDB (φ : Form) : serialSymmSatisfiable φ → finSerialSymmSatisfiable φ := by
  rintro ⟨F, hSer, hSymm, v, w, hw⟩
  exact ⟨filtrationFrame F v φ, inferInstance,
    filtration_preserves_seriality F v φ hSer,
    filtration_preserves_symmetry F v φ hSymm,
    filtrationVal F v φ, ⟦w⟧,
    (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw⟩

/-!
## § 10. FMP Theorems (Transitive Closure Filtration: K4, S4, KD4, KB4, KB5)
-/

/-- **FMP for K4**: Satisfiability in transitive frames implies finite
satisfiability in transitive frames. Uses the transitive closure filtration. -/
theorem fmp_K4 (φ : Form) : transSatisfiable φ → finTransSatisfiable φ := by
  rintro ⟨F, hTrans, v, w, hw⟩
  exact ⟨transFiltrationFrame F v φ, inferInstance,
    transFiltration_transitive F v φ,
    filtrationVal F v φ, ⟦w⟧,
    (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for S4**: Satisfiability in reflexive-transitive frames implies
finite satisfiability in reflexive-transitive frames. -/
theorem fmp_S4 (φ : Form) : refTransSatisfiable φ → finRefTransSatisfiable φ := by
  rintro ⟨F, hRef, hTrans, v, w, hw⟩
  exact ⟨transFiltrationFrame F v φ, inferInstance,
    transFiltration_reflexive F v φ hRef,
    transFiltration_transitive F v φ,
    filtrationVal F v φ, ⟦w⟧,
    (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for KD4**: Satisfiability in serial-transitive frames implies
finite satisfiability in serial-transitive frames. -/
theorem fmp_KD4 (φ : Form) : serialTransSatisfiable φ → finSerialTransSatisfiable φ := by
  rintro ⟨F, hSer, hTrans, v, w, hw⟩
  exact ⟨transFiltrationFrame F v φ, inferInstance,
    transFiltration_serial F v φ hSer,
    transFiltration_transitive F v φ,
    filtrationVal F v φ, ⟦w⟧,
    (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for KB4**: Satisfiability in symmetric-transitive frames implies
finite satisfiability in symmetric-transitive frames. -/
theorem fmp_KB4 (φ : Form) : symmTransSatisfiable φ → finSymmTransSatisfiable φ := by
  rintro ⟨F, hSymm, hTrans, v, w, hw⟩
  exact ⟨transFiltrationFrame F v φ, inferInstance,
    transFiltration_symmetric F v φ hSymm,
    transFiltration_transitive F v φ,
    filtrationVal F v φ, ⟦w⟧,
    (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for KB5**: Satisfiability in symmetric-Euclidean frames implies
finite satisfiability in symmetric-Euclidean frames.
Since symmetric + Euclidean implies transitive, we use the transitive closure
filtration. Since symmetric + transitive implies Euclidean, the result is
also Euclidean. -/
theorem fmp_KB5 (φ : Form) : symmEuclidSatisfiable φ → finSymmEuclidSatisfiable φ := by
  rintro ⟨F, hSymm, hEuclid, v, w, hw⟩
  have hTrans : Transitive F.rel := symm_euclid_imp_trans hSymm hEuclid
  exact ⟨transFiltrationFrame F v φ, inferInstance,
    transFiltration_symmetric F v φ hSymm,
    symm_trans_imp_euclid (transFiltration_symmetric F v φ hSymm) (transFiltration_transitive F v φ),
    filtrationVal F v φ, ⟦w⟧,
    (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw⟩

/-!
## § 11. Validity ↔ Unsatisfiability
-/

theorem k4Valid_iff (φ : Form) : k4Valid φ ↔ ¬ transSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hT, v, w, hw⟩; exact hw (h F hT v w)
  · intro h F hT v w; by_contra hc; exact h ⟨F, hT, v, w, hc⟩

theorem s4Valid_iff (φ : Form) : s4Valid φ ↔ ¬ refTransSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hR, hT, v, w, hw⟩; exact hw (h F hR hT v w)
  · intro h F hR hT v w; by_contra hc; exact h ⟨F, hR, hT, v, w, hc⟩

theorem kd4Valid_iff (φ : Form) : kd4Valid φ ↔ ¬ serialTransSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hS, hT, v, w, hw⟩; exact hw (h F hS hT v w)
  · intro h F hS hT v w; by_contra hc; exact h ⟨F, hS, hT, v, w, hc⟩

theorem ktbValid_iff (φ : Form) : ktbValid φ ↔ ¬ refSymmSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hR, hS, v, w, hw⟩; exact hw (h F hR hS v w)
  · intro h F hR hS v w; by_contra hc; exact h ⟨F, hR, hS, v, w, hc⟩

theorem kdbValid_iff (φ : Form) : kdbValid φ ↔ ¬ serialSymmSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hSer, hS, v, w, hw⟩; exact hw (h F hSer hS v w)
  · intro h F hSer hS v w; by_contra hc; exact h ⟨F, hSer, hS, v, w, hc⟩

theorem kb4Valid_iff (φ : Form) : kb4Valid φ ↔ ¬ symmTransSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hS, hT, v, w, hw⟩; exact hw (h F hS hT v w)
  · intro h F hS hT v w; by_contra hc; exact h ⟨F, hS, hT, v, w, hc⟩

theorem kb5Valid_iff (φ : Form) : kb5Valid φ ↔ ¬ symmEuclidSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hS, hE, v, w, hw⟩; exact hw (h F hS hE v w)
  · intro h F hS hE v w; by_contra hc; exact h ⟨F, hS, hE, v, w, hc⟩

/-!
## § 12. Transfer to Fin n Preserving Frame Conditions
-/

def finNTransSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Transitive rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNRefTransSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Reflexive rel ∧ Transitive rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNSerialTransSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), BasicModal.Serial rel ∧ Transitive rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNRefSymmSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Reflexive rel ∧ Symmetric rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNSerialSymmSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), BasicModal.Serial rel ∧ Symmetric rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNSymmTransSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Symmetric rel ∧ Transitive rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNSymmEuclidSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Symmetric rel ∧ Euclidean rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

/-
Transfer to Fin n preserving transitivity.
-/
lemma finite_model_to_fin_trans {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hTrans : Transitive F.rel) (h : forces F v w φ) :
    finNTransSatisfiable φ (Fintype.card F.states) := by
      refine' ⟨ fun i j => F.rel ( Fintype.equivFin F.states |>.symm i ) ( Fintype.equivFin F.states |>.symm j ), _, _ ⟩ <;> simp_all +decide [ Transitive ];
      · exact fun ⦃x y z⦄ a a_1 => (hTrans a ∘ fun a => a_1) F;
      · refine' ⟨ fun k i => v k ( Fintype.equivFin F.states |>.symm i ), Fintype.equivFin F.states w, _ ⟩;
        convert forces_equiv _ _ _ _ _ using 1;
        any_goals tauto;
        · aesop;
        · aesop

/-
Transfer to Fin n preserving reflexive + transitive.
-/
lemma finite_model_to_fin_ref_trans {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hRef : Reflexive F.rel) (hTrans : Transitive F.rel) (h : forces F v w φ) :
    finNRefTransSatisfiable φ (Fintype.card F.states) := by
      obtain ⟨e, he⟩ : ∃ e : F.states ≃ Fin (Fintype.card F.states), True := by
        exact ⟨ Fintype.equivFin _, trivial ⟩;
      refine' ⟨ fun i j => F.rel ( e.symm i ) ( e.symm j ), _, _, _ ⟩;
      · exact fun i => hRef _;
      · exact fun i j k hij hjk => hTrans hij hjk;
      · refine' ⟨ fun n i => v n ( e.symm i ), e w, _ ⟩;
        convert forces_equiv e _ _ _ _ using 1;
        any_goals tauto;
        · aesop;
        · grind

/-
Transfer to Fin n preserving serial + transitive.
-/
lemma finite_model_to_fin_serial_trans {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSer : BasicModal.Serial F.rel) (hTrans : Transitive F.rel) (h : forces F v w φ) :
    finNSerialTransSatisfiable φ (Fintype.card F.states) := by
      obtain ⟨e, he⟩ : ∃ e : F.states ≃ Fin (Fintype.card F.states), True := by
        exact ⟨ Fintype.equivFin _, trivial ⟩;
      refine' ⟨ fun i j => F.rel ( e.symm i ) ( e.symm j ), _, _, _ ⟩;
      · exact fun i => by obtain ⟨ j, hj ⟩ := hSer ( e.symm i ) ; exact ⟨ e j, by simpa using hj ⟩ ;
      · exact fun i j k hij hjk => hTrans hij hjk;
      · use fun n i => v n ( e.symm i ), e w;
        convert forces_equiv e _ _ _ _ using 1;
        any_goals tauto;
        · aesop;
        · aesop

/-
Transfer to Fin n preserving reflexive + symmetric.
-/
lemma finite_model_to_fin_ref_symm {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hRef : Reflexive F.rel) (hSymm : Symmetric F.rel) (h : forces F v w φ) :
    finNRefSymmSatisfiable φ (Fintype.card F.states) := by
      obtain ⟨e, he⟩ : ∃ e : F.states ≃ Fin (Fintype.card F.states), True := by
        exact ⟨ Fintype.equivFin _, trivial ⟩;
      refine' ⟨ fun i j => F.rel ( e.symm i ) ( e.symm j ), _, _ ⟩ <;> simp_all +decide [ Reflexive, Symmetric ];
      refine' ⟨ fun n i => v n ( e.symm i ), e w, _ ⟩;
      grind +suggestions

/-
Transfer to Fin n preserving serial + symmetric.
-/
lemma finite_model_to_fin_serial_symm {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSer : BasicModal.Serial F.rel) (hSymm : Symmetric F.rel) (h : forces F v w φ) :
    finNSerialSymmSatisfiable φ (Fintype.card F.states) := by
      refine' ⟨ fun i j => F.rel ( Fintype.equivFin _ |>.symm i ) ( Fintype.equivFin _ |>.symm j ), _, _, _ ⟩;
      · intro a; cases' hSer ( ( Fintype.equivFin F.states ).symm a ) with a ha; use ( Fintype.equivFin F.states ) a; aesop;
      · exact fun i j hij => hSymm hij;
      · refine' ⟨ fun n i => v n ( Fintype.equivFin _ |>.symm i ), _, _ ⟩;
        exact Fintype.equivFin F.states w;
        grind +suggestions

/-
Transfer to Fin n preserving symmetric + transitive.
-/
lemma finite_model_to_fin_symm_trans {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSymm : Symmetric F.rel) (hTrans : Transitive F.rel) (h : forces F v w φ) :
    finNSymmTransSatisfiable φ (Fintype.card F.states) := by
      obtain ⟨e, he⟩ : ∃ e : F.states ≃ Fin (Fintype.card F.states), True := by
        exact ⟨ Fintype.equivFin _, trivial ⟩;
      refine' ⟨ fun i j => F.rel ( e.symm i ) ( e.symm j ), _, _, _ ⟩;
      · exact fun i j hij => hSymm hij;
      · exact fun i j k hij hjk => hTrans hij hjk;
      · refine' ⟨ fun n i => v n ( e.symm i ), e w, _ ⟩;
        convert forces_equiv e _ _ _ _ using 1;
        rotate_left;
        exact v;
        exact w;
        exact φ;
        exact fun i j => F.rel ( e.symm i ) ( e.symm j );
        exact fun x y => by simp +decide ;
        exact fun n i => v n ( e.symm i );
        · aesop;
        · aesop

/-
Transfer to Fin n preserving symmetric + Euclidean.
-/
lemma finite_model_to_fin_symm_euclid {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSymm : Symmetric F.rel) (hEuclid : Euclidean F.rel) (h : forces F v w φ) :
    finNSymmEuclidSatisfiable φ (Fintype.card F.states) := by
      have h_equiv : ∃ (e : F.states ≃ Fin (Fintype.card F.states)), Function.Bijective e := by
        exact ⟨ Fintype.equivFin F.states, Fintype.equivFin F.states |>.bijective ⟩;
      -- Define the new relation on Fin (Fintype.card F.states) using the equivalence e.
      obtain ⟨e, he⟩ := h_equiv;
      use fun i j => F.rel (e.symm i) (e.symm j); (
      refine' ⟨ _, _, _ ⟩;
      · exact fun i j hij => hSymm hij;
      · exact fun i j k hij hik => hEuclid hij hik;
      · use fun n i => v n (e.symm i), e w;
        convert forces_equiv e _ _ _ _ |>.1 h;
        · grind +splitIndPred;
        · grind +splitImp)

/-!
## § 13. Bounded Satisfiability
-/

def boundedTransSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNTransSatisfiable φ n

def boundedRefTransSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNRefTransSatisfiable φ n

def boundedSerialTransSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSerialTransSatisfiable φ n

def boundedRefSymmSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNRefSymmSatisfiable φ n

def boundedSerialSymmSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSerialSymmSatisfiable φ n

def boundedSymmTransSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSymmTransSatisfiable φ n

def boundedSymmEuclidSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSymmEuclidSatisfiable φ n

/-!
## § 14. FMP Implies Bounded Satisfiability
-/

theorem transSatisfiable_implies_bounded (φ : Form) :
    transSatisfiable φ → boundedTransSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hTrans, v, w, hw⟩
  have hforces := (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (transFiltrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, transFiltrationFrame_card_le F v φ,
    finite_model_to_fin_trans (transFiltration_transitive F v φ) hforces⟩

theorem refTransSatisfiable_implies_bounded (φ : Form) :
    refTransSatisfiable φ → boundedRefTransSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hRef, hTrans, v, w, hw⟩
  have hforces := (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (transFiltrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, transFiltrationFrame_card_le F v φ,
    finite_model_to_fin_ref_trans (transFiltration_reflexive F v φ hRef)
      (transFiltration_transitive F v φ) hforces⟩

theorem serialTransSatisfiable_implies_bounded (φ : Form) :
    serialTransSatisfiable φ → boundedSerialTransSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSer, hTrans, v, w, hw⟩
  have hforces := (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (transFiltrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, transFiltrationFrame_card_le F v φ,
    finite_model_to_fin_serial_trans (transFiltration_serial F v φ hSer)
      (transFiltration_transitive F v φ) hforces⟩

theorem refSymmSatisfiable_implies_bounded (φ : Form) :
    refSymmSatisfiable φ → boundedRefSymmSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hRef, hSymm, v, w, hw⟩
  have hforces := (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (filtrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F v φ,
    finite_model_to_fin_ref_symm (filtration_preserves_reflexivity F v φ hRef)
      (filtration_preserves_symmetry F v φ hSymm) hforces⟩

theorem serialSymmSatisfiable_implies_bounded (φ : Form) :
    serialSymmSatisfiable φ → boundedSerialSymmSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSer, hSymm, v, w, hw⟩
  have hforces := (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (filtrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F v φ,
    finite_model_to_fin_serial_symm (filtration_preserves_seriality F v φ hSer)
      (filtration_preserves_symmetry F v φ hSymm) hforces⟩

theorem symmTransSatisfiable_implies_bounded (φ : Form) :
    symmTransSatisfiable φ → boundedSymmTransSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSymm, hTrans, v, w, hw⟩
  have hforces := (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (transFiltrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, transFiltrationFrame_card_le F v φ,
    finite_model_to_fin_symm_trans (transFiltration_symmetric F v φ hSymm)
      (transFiltration_transitive F v φ) hforces⟩

theorem symmEuclidSatisfiable_implies_bounded (φ : Form) :
    symmEuclidSatisfiable φ → boundedSymmEuclidSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSymm, hEuclid, v, w, hw⟩
  have hTrans : Transitive F.rel := symm_euclid_imp_trans hSymm hEuclid
  have hforces := (transFiltration_lemma F v φ hTrans w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (transFiltrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, transFiltrationFrame_card_le F v φ,
    finite_model_to_fin_symm_euclid (transFiltration_symmetric F v φ hSymm)
      (symm_trans_imp_euclid (transFiltration_symmetric F v φ hSymm) (transFiltration_transitive F v φ))
      hforces⟩

/-!
## § 15. Decidability of Bounded Satisfiability
-/

noncomputable instance decidable_finNTransSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNTransSatisfiable φ n) := by
  unfold finNTransSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNRefTransSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNRefTransSatisfiable φ n) := by
  unfold finNRefTransSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSerialTransSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSerialTransSatisfiable φ n) := by
  unfold finNSerialTransSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNRefSymmSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNRefSymmSatisfiable φ n) := by
  unfold finNRefSymmSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSerialSymmSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSerialSymmSatisfiable φ n) := by
  unfold finNSerialSymmSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSymmTransSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSymmTransSatisfiable φ n) := by
  unfold finNSymmTransSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSymmEuclidSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSymmEuclidSatisfiable φ n) := by
  unfold finNSymmEuclidSatisfiable; exact Classical.dec _

noncomputable instance decidable_boundedTransSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedTransSatisfiable φ N) := by
  unfold boundedTransSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNTransSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNTransSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedRefTransSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedRefTransSatisfiable φ N) := by
  unfold boundedRefTransSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNRefTransSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNRefTransSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSerialTransSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSerialTransSatisfiable φ N) := by
  unfold boundedSerialTransSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSerialTransSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSerialTransSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedRefSymmSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedRefSymmSatisfiable φ N) := by
  unfold boundedRefSymmSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNRefSymmSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNRefSymmSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSerialSymmSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSerialSymmSatisfiable φ N) := by
  unfold boundedSerialSymmSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSerialSymmSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSerialSymmSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSymmTransSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSymmTransSatisfiable φ N) := by
  unfold boundedSymmTransSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSymmTransSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSymmTransSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSymmEuclidSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSymmEuclidSatisfiable φ N) := by
  unfold boundedSymmEuclidSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSymmEuclidSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSymmEuclidSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

/-!
## § 16. Main Equivalences: Validity ↔ No Bounded Countermodel
-/

theorem k4Valid_iff_no_bounded_countermodel (φ : Form) :
    k4Valid φ ↔ ¬ boundedTransSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [k4Valid_iff]
  constructor
  · intro h hsat
    have : transSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (transSatisfiable_implies_bounded (∼φ) hsat)

theorem s4Valid_iff_no_bounded_countermodel (φ : Form) :
    s4Valid φ ↔ ¬ boundedRefTransSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [s4Valid_iff]
  constructor
  · intro h hsat
    have : refTransSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (refTransSatisfiable_implies_bounded (∼φ) hsat)

theorem kd4Valid_iff_no_bounded_countermodel (φ : Form) :
    kd4Valid φ ↔ ¬ boundedSerialTransSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kd4Valid_iff]
  constructor
  · intro h hsat
    have : serialTransSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (serialTransSatisfiable_implies_bounded (∼φ) hsat)

theorem ktbValid_iff_no_bounded_countermodel (φ : Form) :
    ktbValid φ ↔ ¬ boundedRefSymmSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [ktbValid_iff]
  constructor
  · intro h hsat
    have : refSymmSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (refSymmSatisfiable_implies_bounded (∼φ) hsat)

theorem kdbValid_iff_no_bounded_countermodel (φ : Form) :
    kdbValid φ ↔ ¬ boundedSerialSymmSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kdbValid_iff]
  constructor
  · intro h hsat
    have : serialSymmSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (serialSymmSatisfiable_implies_bounded (∼φ) hsat)

theorem kb4Valid_iff_no_bounded_countermodel (φ : Form) :
    kb4Valid φ ↔ ¬ boundedSymmTransSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kb4Valid_iff]
  constructor
  · intro h hsat
    have : symmTransSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (symmTransSatisfiable_implies_bounded (∼φ) hsat)

theorem kb5Valid_iff_no_bounded_countermodel (φ : Form) :
    kb5Valid φ ↔ ¬ boundedSymmEuclidSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kb5Valid_iff]
  constructor
  · intro h hsat
    have : symmEuclidSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (symmEuclidSatisfiable_implies_bounded (∼φ) hsat)

/-!
## § 17. Decidability
-/

noncomputable instance decidable_k4Valid : DecidablePred k4Valid := by
  intro φ; rw [k4Valid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_s4Valid : DecidablePred s4Valid := by
  intro φ; rw [s4Valid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_kd4Valid : DecidablePred kd4Valid := by
  intro φ; rw [kd4Valid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_ktbValid : DecidablePred ktbValid := by
  intro φ; rw [ktbValid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_kdbValid : DecidablePred kdbValid := by
  intro φ; rw [kdbValid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_kb4Valid : DecidablePred kb4Valid := by
  intro φ; rw [kb4Valid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_kb5Valid : DecidablePred kb5Valid := by
  intro φ; rw [kb5Valid_iff_no_bounded_countermodel]; exact inferInstance

end Modal
