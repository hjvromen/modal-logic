/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Decidability for More Modal Logics

This file extends the decidability result from K to several additional modal logics:
**T** (reflexive frames), **KD** (serial frames), **KB** (symmetric frames),
and **S5** (equivalence frames).

## Method

For T, KD, and KB, the smallest filtration preserves the relevant frame condition,
giving the finite model property. For S5, we use generated subframes to reduce to
frames with universal relation, then filtrate.

The decidability proofs proceed by:
1. Reducing validity to unsatisfiability of the negation
2. Using the FMP to reduce satisfiability to bounded satisfiability
3. The bounded search is decidable (finitely many models to check)

This parallels the structure of `Decidability.lean` (for K), using the same
reduction chain: validity ↔ ¬ bounded satisfiability, with decidability of bounded
satisfiability following from finiteness of the search space.

## Main Results

- `fmp_T`: Finite model property for T (reflexive frames)
- `fmp_KD`: Finite model property for KD (serial frames)
- `fmp_KB`: Finite model property for KB (symmetric frames)
- `fmp_S5`: Finite model property for S5 (equivalence frames)
- `decidable_tValid`: `DecidablePred tValid`
- `decidable_kdValid`: `DecidablePred kdValid`
- `decidable_kbValid`: `DecidablePred kbValid`
- `decidable_s5Valid`: `DecidablePred s5Valid`
-/

import Mathlib
import ModalLogic.Semantics.Decidability

namespace Modal
open Modal
open BasicModal

/-!
## § 1. Validity Definitions
-/

/-- **T-validity**: φ is valid in all reflexive frames. -/
def tValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Reflexive F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KD-validity**: φ is valid in all serial frames. -/
def kdValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), BasicModal.Serial F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KB-validity**: φ is valid in all symmetric frames. -/
def kbValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Symmetric F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **S5-validity**: φ is valid in all equivalence frames. -/
def s5Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Equivalence F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 2. Satisfiability in Frame Classes
-/

def refSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Reflexive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finRefSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Reflexive F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def serialSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), BasicModal.Serial F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finSerialSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ BasicModal.Serial F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def symmSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Symmetric F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finSymmSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Symmetric F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def equivSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Equivalence F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

def finEquivSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Equivalence F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 3. Filtration Preserves Frame Properties
-/

/-- The smallest filtration of a reflexive frame is reflexive. -/
theorem filtration_preserves_reflexivity (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hRef : Reflexive F.rel) :
    Reflexive (filtrationFrame F v φ).rel := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨x, x, subfmlEquiv_refl x, subfmlEquiv_refl x, hRef x⟩

/-- The smallest filtration of a serial frame is serial. -/
theorem filtration_preserves_seriality (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hSer : BasicModal.Serial F.rel) :
    BasicModal.Serial (filtrationFrame F v φ).rel := by
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨y, hxy⟩ := hSer x
  exact ⟨⟦y⟧, x, y, subfmlEquiv_refl x, subfmlEquiv_refl y, hxy⟩

/-- The smallest filtration of a symmetric frame is symmetric. -/
theorem filtration_preserves_symmetry (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (hSymm : Symmetric F.rel) :
    Symmetric (filtrationFrame F v φ).rel := by
  intro q₁ q₂ hrel
  obtain ⟨x₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨x₂, rfl⟩ := Quotient.exists_rep q₂
  obtain ⟨x₁', x₂', hx₁, hx₂, hrel'⟩ := hrel
  exact ⟨x₂', x₁', hx₂, hx₁, hSymm hrel'⟩

/-!
## § 4. FMP for T, KD, KB
-/

/-- **FMP for T**: Satisfiability in reflexive frames implies finite satisfiability
in reflexive frames. -/
theorem fmp_T (φ : Form) : refSatisfiable φ → finRefSatisfiable φ := by
  rintro ⟨F, hRef, v, w, hw⟩
  exact ⟨filtrationFrame F v φ, inferInstance,
    filtration_preserves_reflexivity F v φ hRef,
    filtrationVal F v φ, ⟦w⟧,
    (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for KD** -/
theorem fmp_KD (φ : Form) : serialSatisfiable φ → finSerialSatisfiable φ := by
  rintro ⟨F, hSer, v, w, hw⟩
  exact ⟨filtrationFrame F v φ, inferInstance,
    filtration_preserves_seriality F v φ hSer,
    filtrationVal F v φ, ⟦w⟧,
    (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw⟩

/-- **FMP for KB** -/
theorem fmp_KB (φ : Form) : symmSatisfiable φ → finSymmSatisfiable φ := by
  rintro ⟨F, hSymm, v, w, hw⟩
  exact ⟨filtrationFrame F v φ, inferInstance,
    filtration_preserves_symmetry F v φ hSymm,
    filtrationVal F v φ, ⟦w⟧,
    (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw⟩

/-!
## § 5. FMP for S5
-/

/-- Forces is preserved by generated subframes. -/
theorem forces_subtype {F : Frame} {v : Nat → F.states → Prop}
    {P : F.states → Prop} {w : F.states} {φ : Form} (hw : P w)
    (hclosed : ∀ x y, P x → F.rel x y → P y) :
    forces F v w φ ↔
      forces ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
        (fun n x => v n x.1) ⟨w, hw⟩ φ := by
  induction φ generalizing w with
  | bot => simp [forces]
  | var n => simp [forces]
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [forces]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(ih₁ hw).1 h1, (ih₂ hw).1 h2⟩,
           fun ⟨h1, h2⟩ => ⟨(ih₁ hw).2 h1, (ih₂ hw).2 h2⟩⟩
  | impl ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [forces]
    exact ⟨fun h h' => (ih₂ hw).1 (h ((ih₁ hw).2 h')),
           fun h h' => (ih₂ hw).2 (h ((ih₁ hw).1 h'))⟩
  | box ψ ih =>
    simp only [forces]
    constructor
    · intro h ⟨y, hy⟩ hrel
      exact (ih hy).1 (h y hrel)
    · intro h y hrel
      have hy : P y := hclosed w y hw hrel
      exact (ih hy).2 (h ⟨y, hy⟩ hrel)

/-- **FMP for S5**: Satisfiability in equivalence frames implies finite
satisfiability in equivalence frames. Uses generated subframes. -/
theorem fmp_S5 (φ : Form) : equivSatisfiable φ → finEquivSatisfiable φ := by
  rintro ⟨F, hEquiv, v, w₀, hw₀⟩
  set P := fun s => F.rel w₀ s
  have hw₀P : P w₀ := hEquiv.refl w₀
  have hclosed : ∀ x y, P x → F.rel x y → P y :=
    fun _ _ hx hxy => hEquiv.trans hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : Subtype P) => v n x.1
  have hforces : forces F_sub v_sub ⟨w₀, hw₀P⟩ φ :=
    (forces_subtype hw₀P hclosed).mp hw₀
  have hUniv : ∀ (x y : F_sub.states), F_sub.rel x y :=
    fun ⟨_, hx⟩ ⟨_, hy⟩ => hEquiv.trans (hEquiv.symm hx) hy
  -- Filtrate the subframe
  set filtF := filtrationFrame F_sub v_sub φ
  have hfiltForces := (filtration_lemma F_sub v_sub φ ⟨w₀, hw₀P⟩ φ
    (mem_subformulas_self φ)).mp hforces
  have hfiltUniv : ∀ q₁ q₂ : filtF.states, filtF.rel q₁ q₂ := by
    intro q₁ q₂
    obtain ⟨x₁, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨x₂, rfl⟩ := Quotient.exists_rep q₂
    exact ⟨x₁, x₂, subfmlEquiv_refl x₁, subfmlEquiv_refl x₂, hUniv x₁ x₂⟩
  exact ⟨filtF, inferInstance,
    ⟨fun q => hfiltUniv q q, fun _ => hfiltUniv _ _, fun _ _ => hfiltUniv _ _⟩,
    filtrationVal F_sub v_sub φ, ⟦⟨w₀, hw₀P⟩⟧, hfiltForces⟩

/-!
## § 6. Validity ↔ Unsatisfiability
-/

theorem tValid_iff (φ : Form) : tValid φ ↔ ¬ refSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hRef, v, w, hw⟩; exact hw (h F hRef v w)
  · intro h F hRef v w; by_contra hc; exact h ⟨F, hRef, v, w, hc⟩

theorem kdValid_iff (φ : Form) : kdValid φ ↔ ¬ serialSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hSer, v, w, hw⟩; exact hw (h F hSer v w)
  · intro h F hSer v w; by_contra hc; exact h ⟨F, hSer, v, w, hc⟩

theorem kbValid_iff (φ : Form) : kbValid φ ↔ ¬ symmSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hSymm, v, w, hw⟩; exact hw (h F hSymm v w)
  · intro h F hSymm v w; by_contra hc; exact h ⟨F, hSymm, v, w, hc⟩

theorem s5Valid_iff (φ : Form) : s5Valid φ ↔ ¬ equivSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hEquiv, v, w, hw⟩; exact hw (h F hEquiv v w)
  · intro h F hEquiv v w; by_contra hc; exact h ⟨F, hEquiv, v, w, hc⟩

/-!
## § 7. FMP as biconditionals
-/

theorem refSatisfiable_iff_fin (φ : Form) : refSatisfiable φ ↔ finRefSatisfiable φ :=
  ⟨fmp_T φ, fun ⟨F, _, h, v, w, hw⟩ => ⟨F, h, v, w, hw⟩⟩

theorem serialSatisfiable_iff_fin (φ : Form) : serialSatisfiable φ ↔ finSerialSatisfiable φ :=
  ⟨fmp_KD φ, fun ⟨F, _, h, v, w, hw⟩ => ⟨F, h, v, w, hw⟩⟩

theorem symmSatisfiable_iff_fin (φ : Form) : symmSatisfiable φ ↔ finSymmSatisfiable φ :=
  ⟨fmp_KB φ, fun ⟨F, _, h, v, w, hw⟩ => ⟨F, h, v, w, hw⟩⟩

theorem equivSatisfiable_iff_fin (φ : Form) : equivSatisfiable φ ↔ finEquivSatisfiable φ :=
  ⟨fmp_S5 φ, fun ⟨F, _, h, v, w, hw⟩ => ⟨F, h, v, w, hw⟩⟩

/-!
## § 8. Transfer to Fin n preserving frame conditions

The `forces_equiv` lemma from `Decidability.lean` shows that forcing is preserved
under frame isomorphisms. We use `Fintype.equivFin` to transfer finite models
to `Fin n`, explicitly tracking that the transferred relation inherits frame
conditions from the original.
-/

/-- Satisfiability in a reflexive frame on Fin n. -/
def finNRefSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Reflexive rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n),
      forces ⟨Fin n, rel⟩ v w φ

/-- Satisfiability in a serial frame on Fin n. -/
def finNSerialSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), BasicModal.Serial rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n),
      forces ⟨Fin n, rel⟩ v w φ

/-- Satisfiability in a symmetric frame on Fin n. -/
def finNSymmSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Symmetric rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n),
      forces ⟨Fin n, rel⟩ v w φ

/-- Satisfiability in an equivalence frame on Fin n. -/
def finNEquivSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Equivalence rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n),
      forces ⟨Fin n, rel⟩ v w φ

/-
Transferring a model on a finite type to `Fin n` preserves reflexivity.
-/
lemma finite_model_to_fin_ref {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hRef : Reflexive F.rel) (h : forces F v w φ) :
    finNRefSatisfiable φ (Fintype.card F.states) := by
  use fun i j => F.rel (Fintype.equivFin F.states |>.symm i) (Fintype.equivFin F.states |>.symm j);
  use fun x => hRef _;
  use fun n i => v n (Fintype.equivFin F.states |>.symm i), Fintype.equivFin F.states w;
  grind +suggestions

/-
Transferring a model on a finite type to `Fin n` preserves seriality.
-/
lemma finite_model_to_fin_serial {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSer : BasicModal.Serial F.rel) (h : forces F v w φ) :
    finNSerialSatisfiable φ (Fintype.card F.states) := by
  refine' ⟨ fun i j => F.rel ( Fintype.equivFin F.states |>.symm i ) ( Fintype.equivFin F.states |>.symm j ), _, _ ⟩;
  · intro i; cases' hSer ( Fintype.equivFin F.states |>.symm i ) with j hj; use Fintype.equivFin F.states j; aesop;
  · refine' ⟨ fun n i => v n ( Fintype.equivFin F.states |>.symm i ), Fintype.equivFin F.states w, _ ⟩;
    refine' forces_equiv _ _ _ _ _ |>.1 h;
    · aesop;
    · grind

/-
Transferring a model on a finite type to `Fin n` preserves symmetry.
-/
lemma finite_model_to_fin_symm {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSymm : Symmetric F.rel) (h : forces F v w φ) :
    finNSymmSatisfiable φ (Fintype.card F.states) := by
  refine' ⟨ fun i j => F.rel ( Fintype.equivFin _ |>.symm i ) ( Fintype.equivFin _ |>.symm j ), _, _ ⟩;
  · exact fun i j hij => hSymm hij;
  · refine' ⟨ fun k i => v k ( Fintype.equivFin _ |>.symm i ), _, _ ⟩;
    exact ( Fintype.equivFin F.states ) w;
    grind +suggestions

/-
Transferring a model on a finite type to `Fin n` preserves equivalence.
-/
lemma finite_model_to_fin_equiv {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hEquiv : Equivalence F.rel) (h : forces F v w φ) :
    finNEquivSatisfiable φ (Fintype.card F.states) := by
  refine' ⟨ fun i j => F.rel ( Fintype.equivFin F.states |>.symm i ) ( Fintype.equivFin F.states |>.symm j ), _, _ ⟩;
  · exact Equivalence.comap hEquiv ⇑(Fintype.equivFin F.states).symm;
  · use fun n i => v n (Fintype.equivFin F.states |>.symm i), Fintype.equivFin F.states w;
    convert forces_equiv ( Fintype.equivFin F.states ) _ _ _ _ |>.1 h using 1;
    · aesop;
    · grind +revert

/-!
## § 9. Filtration cardinality bound

The number of equivalence classes in any filtration is bounded by 2^|Sub(φ)|,
since each class is determined by a truth assignment to the subformulas.
This bound is independent of any frame condition.
-/

/-
The filtration frame has at most 2^|Sub(φ)| states.
-/
lemma filtrationFrame_card_le (F : Frame)
    (v : Nat → F.states → Prop) (φ : Form) :
    @Fintype.card (filtrationFrame F v φ).states (Fintype.ofFinite _) ≤
      2 ^ (subformulas φ).length := by
  -- The function is injective, so the cardinality of the image is less than or equal to the cardinality of the domain.
  have h_inj : Function.Injective (fun q : (filtrationFrame F v φ).states => fun ψ : (subformulas φ).toFinset => forces F v q.out ψ) := by
    intros q1 q2 h_eq;
    rw [ ← Quotient.out_eq q1, ← Quotient.out_eq q2 ];
    exact Quotient.sound fun ψ hψ => by specialize h_eq; replace h_eq := congr_fun h_eq ⟨ ψ, by aesop ⟩ ; aesop;
  refine' le_trans _ ( pow_le_pow_right₀ ( by decide ) ( List.toFinset_card_le _ ) );
  convert Fintype.card_le_of_injective _ h_inj using 1;
  simp +decide [ Fintype.card_pi ];
  rw [ Fintype.card_of_subtype ] ; aesop

/-!
## § 10. Bounded Satisfiability for Constrained Classes
-/

/-- Bounded satisfiability in reflexive frames. -/
def boundedRefSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNRefSatisfiable φ n

/-- Bounded satisfiability in serial frames. -/
def boundedSerialSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSerialSatisfiable φ n

/-- Bounded satisfiability in symmetric frames. -/
def boundedSymmSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSymmSatisfiable φ n

/-- Bounded satisfiability in equivalence frames. -/
def boundedEquivSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNEquivSatisfiable φ n

/-!
## § 11. FMP implies bounded satisfiability

Each proof goes directly from satisfiability in the frame class through
filtration (which preserves the frame condition and is bounded) to
bounded satisfiability on Fin n.
-/

/-- Reflexive satisfiability implies bounded reflexive satisfiability. -/
theorem refSatisfiable_implies_bounded (φ : Form) :
    refSatisfiable φ → boundedRefSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hRef, v, w, hw⟩
  have hRef' := filtration_preserves_reflexivity F v φ hRef
  have hforces := (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (filtrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F v φ,
    finite_model_to_fin_ref hRef' hforces⟩

/-- Serial satisfiability implies bounded serial satisfiability. -/
theorem serialSatisfiable_implies_bounded (φ : Form) :
    serialSatisfiable φ → boundedSerialSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSer, v, w, hw⟩
  have hSer' := filtration_preserves_seriality F v φ hSer
  have hforces := (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (filtrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F v φ,
    finite_model_to_fin_serial hSer' hforces⟩

/-- Symmetric satisfiability implies bounded symmetric satisfiability. -/
theorem symmSatisfiable_implies_bounded (φ : Form) :
    symmSatisfiable φ → boundedSymmSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSymm, v, w, hw⟩
  have hSymm' := filtration_preserves_symmetry F v φ hSymm
  have hforces := (filtration_lemma F v φ w φ (mem_subformulas_self φ)).mp hw
  letI : Fintype (filtrationFrame F v φ).states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F v φ,
    finite_model_to_fin_symm hSymm' hforces⟩

/-- Equivalence satisfiability implies bounded equivalence satisfiability. -/
theorem equivSatisfiable_implies_bounded (φ : Form) :
    equivSatisfiable φ → boundedEquivSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hEquiv, v, w₀, hw₀⟩
  -- Use the S5 FMP: restrict to equivalence class, get universal relation, filtrate
  set P := fun s => F.rel w₀ s
  have hw₀P : P w₀ := hEquiv.refl w₀
  have hclosed : ∀ x y, P x → F.rel x y → P y :=
    fun _ _ hx hxy => hEquiv.trans hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : Subtype P) => v n x.1
  have hforces : forces F_sub v_sub ⟨w₀, hw₀P⟩ φ :=
    (forces_subtype hw₀P hclosed).mp hw₀
  have hUniv : ∀ (x y : F_sub.states), F_sub.rel x y :=
    fun ⟨_, hx⟩ ⟨_, hy⟩ => hEquiv.trans (hEquiv.symm hx) hy
  have hfiltForces := (filtration_lemma F_sub v_sub φ ⟨w₀, hw₀P⟩ φ
    (mem_subformulas_self φ)).mp hforces
  have hfiltUniv : ∀ q₁ q₂ : (filtrationFrame F_sub v_sub φ).states,
      (filtrationFrame F_sub v_sub φ).rel q₁ q₂ := by
    intro q₁ q₂
    obtain ⟨x₁, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨x₂, rfl⟩ := Quotient.exists_rep q₂
    exact ⟨x₁, x₂, subfmlEquiv_refl x₁, subfmlEquiv_refl x₂, hUniv x₁ x₂⟩
  have hfiltEquiv : Equivalence (filtrationFrame F_sub v_sub φ).rel :=
    ⟨fun q => hfiltUniv q q, fun _ => hfiltUniv _ _, fun _ _ => hfiltUniv _ _⟩
  letI : Fintype (filtrationFrame F_sub v_sub φ).states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F_sub v_sub φ,
    finite_model_to_fin_equiv hfiltEquiv hfiltForces⟩

/-!
## § 12. Decidability of bounded constrained satisfiability

Each `finN*Satisfiable` predicate is decidable because it quantifies over
finite types (relations, valuations, and worlds on `Fin n`). The frame
conditions (reflexivity, seriality, symmetry, equivalence) are decidable
properties of finite relations. We use `Classical.dec` at the inner level,
matching the approach in `Decidability.lean` for K.
-/

noncomputable instance decidable_finNRefSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNRefSatisfiable φ n) := by
  unfold finNRefSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSerialSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSerialSatisfiable φ n) := by
  unfold finNSerialSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSymmSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSymmSatisfiable φ n) := by
  unfold finNSymmSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNEquivSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNEquivSatisfiable φ n) := by
  unfold finNEquivSatisfiable; exact Classical.dec _

noncomputable instance decidable_boundedRefSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedRefSatisfiable φ N) := by
  unfold boundedRefSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNRefSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNRefSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSerialSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSerialSatisfiable φ N) := by
  unfold boundedSerialSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSerialSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSerialSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSymmSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSymmSatisfiable φ N) := by
  unfold boundedSymmSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSymmSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSymmSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedEquivSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedEquivSatisfiable φ N) := by
  unfold boundedEquivSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNEquivSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNEquivSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

/-!
## § 13. Main equivalences: validity ↔ no bounded countermodel
-/

/-- **T-validity ↔ no bounded reflexive countermodel** -/
theorem tValid_iff_no_bounded_countermodel (φ : Form) :
    tValid φ ↔ ¬ boundedRefSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [tValid_iff]
  constructor
  · intro h hsat
    have : refSatisfiable (∼φ) :=
      match hsat with
      | ⟨n, _, rel, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (refSatisfiable_implies_bounded (∼φ) hsat)

/-- **KD-validity ↔ no bounded serial countermodel** -/
theorem kdValid_iff_no_bounded_countermodel (φ : Form) :
    kdValid φ ↔ ¬ boundedSerialSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kdValid_iff]
  constructor
  · intro h hsat
    have : serialSatisfiable (∼φ) :=
      match hsat with
      | ⟨n, _, rel, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (serialSatisfiable_implies_bounded (∼φ) hsat)

/-- **KB-validity ↔ no bounded symmetric countermodel** -/
theorem kbValid_iff_no_bounded_countermodel (φ : Form) :
    kbValid φ ↔ ¬ boundedSymmSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kbValid_iff]
  constructor
  · intro h hsat
    have : symmSatisfiable (∼φ) :=
      match hsat with
      | ⟨n, _, rel, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (symmSatisfiable_implies_bounded (∼φ) hsat)

/-- **S5-validity ↔ no bounded equivalence countermodel** -/
theorem s5Valid_iff_no_bounded_countermodel (φ : Form) :
    s5Valid φ ↔ ¬ boundedEquivSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [s5Valid_iff]
  constructor
  · intro h hsat
    have : equivSatisfiable (∼φ) :=
      match hsat with
      | ⟨n, _, rel, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (equivSatisfiable_implies_bounded (∼φ) hsat)

/-!
## § 14. Decidability

The decision procedure for each logic:
1. φ is valid ↔ ∼φ is not satisfiable in the frame class
2. By FMP, satisfiability reduces to bounded satisfiability (§ 11)
3. Bounded satisfiability is decidable by finite search (§ 12)

The `noncomputable` marker is due to the use of `Classical.choice` in the
finite model property proof (Lindenbaum's lemma). The decision procedure
itself is conceptually computable.
-/

/-- **Decidability of T-validity**: Given any modal formula φ, we can determine
whether φ is valid in all reflexive frames. The decision procedure reduces
to bounded search via the finite model property for T. -/
noncomputable instance decidable_tValid : DecidablePred tValid := by
  intro φ
  rw [tValid_iff_no_bounded_countermodel]
  exact inferInstance

/-- **Decidability of KD-validity**: Given any modal formula φ, we can determine
whether φ is valid in all serial frames. The decision procedure reduces
to bounded search via the finite model property for KD. -/
noncomputable instance decidable_kdValid : DecidablePred kdValid := by
  intro φ
  rw [kdValid_iff_no_bounded_countermodel]
  exact inferInstance

/-- **Decidability of KB-validity**: Given any modal formula φ, we can determine
whether φ is valid in all symmetric frames. The decision procedure reduces
to bounded search via the finite model property for KB. -/
noncomputable instance decidable_kbValid : DecidablePred kbValid := by
  intro φ
  rw [kbValid_iff_no_bounded_countermodel]
  exact inferInstance

/-- **Decidability of S5-validity**: Given any modal formula φ, we can determine
whether φ is valid in all equivalence frames. The decision procedure reduces
to bounded search via the finite model property for S5. -/
noncomputable instance decidable_s5Valid : DecidablePred s5Valid := by
  intro φ
  rw [s5Valid_iff_no_bounded_countermodel]
  exact inferInstance

end Modal