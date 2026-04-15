/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Finite Model Property and Decidability for K45 and KD45

This file proves the finite model property (FMP) and decidability for:
- **K45** (transitive + Euclidean frames)
- **KD45** (serial + transitive + Euclidean frames)

## Method: Euclidean Generated Subframe + Smallest Filtration

We reuse the Euclidean generated subframe technique from `FMPEuclidean.lean`:

1. Restrict to the subframe P = {w₀} ∪ C₁ where C₁ = {z | ∃y, R(w₀,y) ∧ R(y,z)}.
2. In a transitive + Euclidean frame, C₁ equals the successor set {z | R(w₀,z)}
   and is a cluster (all elements pairwise related).
3. The smallest filtration of this subframe preserves:
   - **Euclidean** (proven in `FMPEuclidean.lean`)
   - **Transitivity** (proven here): any P-element sees any C₁-element,
     so transitivity chains through the filtration are preserved.
   - **Seriality** (inherited from the standard filtration result)

### Key structural property

In a transitive + Euclidean frame, any P-element sees any C₁-element:
- If a ∈ C₁: the cluster property gives R(a, c) for any c ∈ C₁.
- If a = w₀: since c ∈ C₁ means ∃y, R(w₀,y) ∧ R(y,c), transitivity gives R(w₀,c).

This directly yields transitivity of the filtration: given [a] R_s [b] R_s [c],
the witnesses b₁ and c₁ both lie in C₁, and R(a₁, c₁) follows from the above.

## Main Results

- `fmp_K45`: FMP for K45 (transitive + Euclidean frames)
- `fmp_KD45`: FMP for KD45 (serial + transitive + Euclidean frames)
- `decidable_k45Valid`: `DecidablePred k45Valid`
- `decidable_kd45Valid`: `DecidablePred kd45Valid`

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §2.3
- Chellas, *Modal Logic: An Introduction*, Ch. 5
-/

import Mathlib
import ModalLogic.Semantics.FMPEuclidean

namespace Modal
open Modal
open BasicModal

/-!
## § 1. Structural Lemma: P-elements see C₁-elements

In a transitive + Euclidean frame, any element of P = {w₀} ∪ C₁ sees any
element of C₁. This is the key structural property that makes the smallest
filtration of the Euclidean subframe transitive.
-/

/-
In a transitive + Euclidean frame, any P-element sees any C₁-element.
    If a ∈ P (a = w₀ or a ∈ C₁) and c ∈ C₁, then R(a, c).
-/
lemma transEuclid_P_sees_cluster {α : Type*} {R : α → α → Prop}
    (hT : Transitive R) (hE : Euclidean R)
    {w₀ a c : α}
    (ha : a = w₀ ∨ ∃ y, R w₀ y ∧ R y a)
    (hc : ∃ y, R w₀ y ∧ R y c) :
    R a c := by
  cases' ha with ha ha;
  · exact ha ▸ hT hc.choose_spec.1 hc.choose_spec.2;
  · exact euclid_cluster' hE ha.choose_spec.1 ha.choose_spec.2 hc.choose_spec.1 hc.choose_spec.2

/-!
## § 2. The Smallest Filtration of the Euclidean Subframe is Transitive
-/

/-
The smallest filtration of the Euclidean generated subframe preserves
    transitivity when the original frame is transitive + Euclidean.

    Proof: Given [a] R_s [b] R_s [c], extract witnesses a₁, b₁, b₂, c₁.
    Since b₁ and c₁ are successors in the subframe, they lie in C₁.
    By `transEuclid_P_sees_cluster`, R(a₁, c₁), giving [a] R_s [c].
-/
theorem euclidSubframe_filtration_transitive (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) (w₀ : F.states) (hT : Transitive F.rel) (hE : Euclidean F.rel) :
    let P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w
    let F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
    let v_sub := fun n (x : F_sub.states) => v n x.1
    Transitive (filtrationFrame F_sub v_sub φ).rel := by
  simp_all +decide [ Transitive ];
  intro x y z;
  rcases x with ⟨ x, hx ⟩ ; rcases y with ⟨ y, hy ⟩ ; rcases z with ⟨ z, hz ⟩ ; simp_all +decide ;
  rintro ⟨ a, b, ha, hb, hab ⟩ ⟨ c, d, hc, hd, hcd ⟩;
  refine' ⟨ a, d, _, _, _ ⟩;
  · exact ha;
  · exact hd;
  · apply transEuclid_P_sees_cluster hT hE;
    exact a.2;
    grind +splitImp

/-!
## § 3. Validity and Satisfiability Definitions
-/

/-- **K45-validity**: φ is valid in all transitive-Euclidean frames. -/
def k45Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Transitive F.rel → Euclidean F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KD45-validity**: φ is valid in all serial-transitive-Euclidean frames. -/
def kd45Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), BasicModal.Serial F.rel → Transitive F.rel → Euclidean F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Satisfiability in transitive-Euclidean frames. -/
def transEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Transitive F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Finite satisfiability in transitive-Euclidean frames. -/
def finTransEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Transitive F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Satisfiability in serial-transitive-Euclidean frames. -/
def serialTransEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), BasicModal.Serial F.rel ∧ Transitive F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Finite satisfiability in serial-transitive-Euclidean frames. -/
def finSerialTransEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ BasicModal.Serial F.rel ∧ Transitive F.rel ∧
    Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 4. FMP for K45 and KD45
-/

/-- **FMP for K45**: Satisfiability in transitive-Euclidean frames implies
finite satisfiability in transitive-Euclidean frames. -/
theorem fmp_K45 (φ : Form) : transEuclidSatisfiable φ → finTransEuclidSatisfiable φ := by
  rintro ⟨F, hTrans, hEuclid, v, w₀, hw₀⟩
  set P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w with hP_def
  have hP_w₀ : P w₀ := Or.inl rfl
  have hP_closed : ∀ x y, P x → F.rel x y → P y := fun x y hx hxy =>
    euclidReachable_closed' F w₀ hEuclid hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : F_sub.states) => v n x.1
  have hforces_sub : forces F_sub v_sub ⟨w₀, hP_w₀⟩ φ :=
    (forces_subtype hP_w₀ hP_closed).mp hw₀
  set filtF := filtrationFrame F_sub v_sub φ
  have hfilt_forces := (filtration_lemma F_sub v_sub φ ⟨w₀, hP_w₀⟩ φ
    (mem_subformulas_self φ)).mp hforces_sub
  exact ⟨filtF, inferInstance,
    euclidSubframe_filtration_transitive F v φ w₀ hTrans hEuclid,
    euclidSubframe_filtration_euclidean F v φ w₀ hEuclid,
    filtrationVal F_sub v_sub φ, ⟦⟨w₀, hP_w₀⟩⟧, hfilt_forces⟩

/-- **FMP for KD45**: Satisfiability in serial-transitive-Euclidean frames implies
finite satisfiability in serial-transitive-Euclidean frames. -/
theorem fmp_KD45 (φ : Form) :
    serialTransEuclidSatisfiable φ → finSerialTransEuclidSatisfiable φ := by
  rintro ⟨F, hSerial, hTrans, hEuclid, v, w₀, hw₀⟩
  set P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w with hP_def
  have hP_w₀ : P w₀ := Or.inl rfl
  have hP_closed : ∀ x y, P x → F.rel x y → P y := fun x y hx hxy =>
    euclidReachable_closed' F w₀ hEuclid hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : F_sub.states) => v n x.1
  have hforces_sub : forces F_sub v_sub ⟨w₀, hP_w₀⟩ φ :=
    (forces_subtype hP_w₀ hP_closed).mp hw₀
  have hSub_serial : BasicModal.Serial F_sub.rel := by
    intro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hSerial x
    exact ⟨⟨y, hP_closed x y hx hy⟩, hy⟩
  set filtF := filtrationFrame F_sub v_sub φ
  have hfilt_forces := (filtration_lemma F_sub v_sub φ ⟨w₀, hP_w₀⟩ φ
    (mem_subformulas_self φ)).mp hforces_sub
  exact ⟨filtF, inferInstance,
    filtration_preserves_seriality F_sub v_sub φ hSub_serial,
    euclidSubframe_filtration_transitive F v φ w₀ hTrans hEuclid,
    euclidSubframe_filtration_euclidean F v φ w₀ hEuclid,
    filtrationVal F_sub v_sub φ, ⟦⟨w₀, hP_w₀⟩⟧, hfilt_forces⟩

/-!
## § 5. Validity ↔ Unsatisfiability
-/

theorem k45Valid_iff (φ : Form) : k45Valid φ ↔ ¬ transEuclidSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hT, hE, v, w, hw⟩; exact hw (h F hT hE v w)
  · intro h F hT hE v w; by_contra hc; exact h ⟨F, hT, hE, v, w, hc⟩

theorem kd45Valid_iff (φ : Form) : kd45Valid φ ↔ ¬ serialTransEuclidSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hS, hT, hE, v, w, hw⟩; exact hw (h F hS hT hE v w)
  · intro h F hS hT hE v w; by_contra hc; exact h ⟨F, hS, hT, hE, v, w, hc⟩

/-!
## § 6. Transfer to Fin n
-/

def finNTransEuclidSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Transitive rel ∧ Euclidean rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNSerialTransEuclidSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), BasicModal.Serial rel ∧ Transitive rel ∧
    Euclidean rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

/-
Transfer to Fin n preserving transitive + Euclidean.
-/
lemma finite_model_to_fin_trans_euclid {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hTrans : Transitive F.rel) (hEuclid : Euclidean F.rel)
    (h : forces F v w φ) :
    finNTransEuclidSatisfiable φ (Fintype.card F.states) := by
  obtain ⟨e, he⟩ : ∃ (e : F.states ≃ Fin (Fintype.card F.states)), Function.Bijective e := ⟨ Fintype.equivFin F.states, Fintype.equivFin F.states |>.bijective ⟩;
  use fun i j => F.rel (e.symm i) (e.symm j);
  refine' ⟨ _, _, _ ⟩;
  · exact fun i j k hij hjk => hTrans hij hjk;
  · exact fun i j k hij hjk => hEuclid hij hjk;
  · use fun n i => v n ( e.symm i ), e w;
    convert forces_equiv e _ _ _ _ |>.1 h;
    · grind;
    · grind +extAll

/-
Transfer to Fin n preserving serial + transitive + Euclidean.
-/
lemma finite_model_to_fin_serial_trans_euclid {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSerial : BasicModal.Serial F.rel) (hTrans : Transitive F.rel)
    (hEuclid : Euclidean F.rel)
    (h : forces F v w φ) :
    finNSerialTransEuclidSatisfiable φ (Fintype.card F.states) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact fun i j => F.rel ( Fintype.equivFin F.states |>.symm i ) ( Fintype.equivFin F.states |>.symm j );
  · intro i; obtain ⟨ j, hj ⟩ := hSerial ( Fintype.equivFin F.states |>.symm i ) ; use Fintype.equivFin F.states j; aesop;
  · exact fun i j k hij hjk => hTrans hij hjk;
  · exact fun i j k hij hjk => hEuclid hij hjk;
  · refine' ⟨ fun n i => v n ( Fintype.equivFin F.states |>.symm i ), Fintype.equivFin F.states w, _ ⟩;
    convert forces_equiv ( Fintype.equivFin F.states ) _ _ _ _ |>.1 h using 1;
    · aesop;
    · aesop

/-!
## § 7. Bounded Satisfiability
-/

def boundedTransEuclidSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNTransEuclidSatisfiable φ n

def boundedSerialTransEuclidSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSerialTransEuclidSatisfiable φ n

/-!
## § 8. FMP Implies Bounded Satisfiability
-/

theorem transEuclidSatisfiable_implies_bounded (φ : Form) :
    transEuclidSatisfiable φ →
    boundedTransEuclidSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hTrans, hEuclid, v, w₀, hw₀⟩
  set P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w
  have hP_w₀ : P w₀ := Or.inl rfl
  have hP_closed : ∀ x y, P x → F.rel x y → P y := fun x y hx hxy =>
    euclidReachable_closed' F w₀ hEuclid hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : F_sub.states) => v n x.1
  have hforces_sub : forces F_sub v_sub ⟨w₀, hP_w₀⟩ φ :=
    (forces_subtype hP_w₀ hP_closed).mp hw₀
  set filtF := filtrationFrame F_sub v_sub φ
  have hfilt_forces := (filtration_lemma F_sub v_sub φ ⟨w₀, hP_w₀⟩ φ
    (mem_subformulas_self φ)).mp hforces_sub
  letI : Fintype filtF.states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F_sub v_sub φ,
    finite_model_to_fin_trans_euclid
      (euclidSubframe_filtration_transitive F v φ w₀ hTrans hEuclid)
      (euclidSubframe_filtration_euclidean F v φ w₀ hEuclid)
      hfilt_forces⟩

theorem serialTransEuclidSatisfiable_implies_bounded (φ : Form) :
    serialTransEuclidSatisfiable φ →
    boundedSerialTransEuclidSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSerial, hTrans, hEuclid, v, w₀, hw₀⟩
  set P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w
  have hP_w₀ : P w₀ := Or.inl rfl
  have hP_closed : ∀ x y, P x → F.rel x y → P y := fun x y hx hxy =>
    euclidReachable_closed' F w₀ hEuclid hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : F_sub.states) => v n x.1
  have hforces_sub : forces F_sub v_sub ⟨w₀, hP_w₀⟩ φ :=
    (forces_subtype hP_w₀ hP_closed).mp hw₀
  have hSub_serial : BasicModal.Serial F_sub.rel := by
    intro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hSerial x
    exact ⟨⟨y, hP_closed x y hx hy⟩, hy⟩
  set filtF := filtrationFrame F_sub v_sub φ
  have hfilt_forces := (filtration_lemma F_sub v_sub φ ⟨w₀, hP_w₀⟩ φ
    (mem_subformulas_self φ)).mp hforces_sub
  letI : Fintype filtF.states := Fintype.ofFinite _
  exact ⟨_, filtrationFrame_card_le F_sub v_sub φ,
    finite_model_to_fin_serial_trans_euclid
      (filtration_preserves_seriality F_sub v_sub φ hSub_serial)
      (euclidSubframe_filtration_transitive F v φ w₀ hTrans hEuclid)
      (euclidSubframe_filtration_euclidean F v φ w₀ hEuclid)
      hfilt_forces⟩

/-!
## § 9. Decidability of Bounded Satisfiability
-/

noncomputable instance decidable_finNTransEuclidSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNTransEuclidSatisfiable φ n) := by
  unfold finNTransEuclidSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSerialTransEuclidSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSerialTransEuclidSatisfiable φ n) := by
  unfold finNSerialTransEuclidSatisfiable; exact Classical.dec _

noncomputable instance decidable_boundedTransEuclidSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedTransEuclidSatisfiable φ N) := by
  unfold boundedTransEuclidSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNTransEuclidSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNTransEuclidSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSerialTransEuclidSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSerialTransEuclidSatisfiable φ N) := by
  unfold boundedSerialTransEuclidSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSerialTransEuclidSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSerialTransEuclidSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

/-!
## § 10. Main Equivalences: Validity ↔ No Bounded Countermodel
-/

theorem k45Valid_iff_no_bounded_countermodel (φ : Form) :
    k45Valid φ ↔
    ¬ boundedTransEuclidSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [k45Valid_iff]
  constructor
  · intro h hsat
    have : transEuclidSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (transEuclidSatisfiable_implies_bounded (∼φ) hsat)

theorem kd45Valid_iff_no_bounded_countermodel (φ : Form) :
    kd45Valid φ ↔
    ¬ boundedSerialTransEuclidSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kd45Valid_iff]
  constructor
  · intro h hsat
    have : serialTransEuclidSatisfiable (∼φ) :=
      match hsat with
      | ⟨n, _, rel, _, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (serialTransEuclidSatisfiable_implies_bounded (∼φ) hsat)

/-!
## § 11. Decidability
-/

noncomputable instance decidable_k45Valid : DecidablePred k45Valid := by
  intro φ; rw [k45Valid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_kd45Valid : DecidablePred kd45Valid := by
  intro φ; rw [kd45Valid_iff_no_bounded_countermodel]; exact inferInstance

end Modal