/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Finite Model Property and Decidability for K5 and KD5

This file proves the finite model property (FMP) and decidability for:
- **K5** (Euclidean frames)
- **KD5** (serial + Euclidean frames)

## Method: Generated Subframe + Filtration

The smallest filtration does NOT preserve the Euclidean property in general,
and the largest filtration also fails (a counterexample is documented in
`IMPLEMENTATION_PLAN_FMP_K5.md`). Instead, we use a two-step construction:

### Step 1: Restrict to a generated subframe
Given a Euclidean model satisfying φ at w₀, we restrict to the **Euclidean
generated subframe** P = {w₀} ∪ C₁, where:
  C₁ = {z | ∃ y, R(w₀, y) ∧ R(y, z)}
This set is R-closed (any successor of a P-element is in C₁), and within C₁,
ALL elements are pairwise related (a "cluster"). Truth is preserved by the
standard generated subframe theorem (`forces_subtype`).

### Step 2: Apply the smallest filtration
The filtration of this subframe IS Euclidean. The key argument: whenever
[a] R_s [b] in the filtration, the witness b' lies in C₁ (because any
successor in P is in C₁). Similarly for [a] R_s [c]. Since C₁ is a cluster,
R(b', c'), giving [b] R_s [c]. So Euclidean is preserved.

### Structural properties of Euclidean frames used
1. **Successors are reflexive**: R(w,x) → R(x,x) (Euclidean with y=z=x).
2. **Successors of successors land in C₁**: R(w₀,y) ∧ R(y,z) → z ∈ C₁.
3. **C₁ is a cluster**: z₁, z₂ ∈ C₁ → R(z₁, z₂).
4. **C₁ is R-closed**: z ∈ C₁ ∧ R(z,u) → u ∈ C₁.
5. **No back-edges when w₀ ∉ C₁**: ¬R(w₀,w₀) → ∀c ∈ C₁, ¬R(c, w₀).

## Main Results

- `fmp_K5`: FMP for K5 (Euclidean frames)
- `fmp_KD5`: FMP for KD5 (serial + Euclidean frames)
- `decidable_k5Valid`: `DecidablePred k5Valid`
- `decidable_kd5Valid`: `DecidablePred kd5Valid`

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §2.3
- Chellas, *Modal Logic: An Introduction*, Ch. 5
-/

import Mathlib
import ModalLogic.Semantics.FMPDecidabilityAll
import ModalLogic.Semantics.LargestFiltration

namespace Modal
open Modal
open BasicModal

/-!
## § 1. Euclidean Cluster Lemmas

In a Euclidean frame, the successors of any world form a cluster: they are all
pairwise related. More specifically, the "two-step reachable" set
C₁ = {z | ∃ y, R(w₀, y) ∧ R(y, z)} is a cluster and is R-closed.
-/

/-- In a Euclidean frame, every successor is reflexive. -/
lemma euclid_succ_refl' {α : Type*} {R : α → α → Prop}
    (hE : Euclidean R) {w x : α} (h : R w x) : R x x :=
  hE h h

/-- In a Euclidean frame, the two-step reachable set C₁ is a cluster:
    if z₁ and z₂ are both in C₁, then R(z₁, z₂). -/
lemma euclid_cluster' {α : Type*} {R : α → α → Prop}
    (hE : Euclidean R) {w₀ y₁ z₁ y₂ z₂ : α}
    (h1 : R w₀ y₁) (h2 : R y₁ z₁)
    (h3 : R w₀ y₂) (h4 : R y₂ z₂) :
    R z₁ z₂ := by
  have h_y₁y₂ : R y₁ y₂ := hE h1 h3
  have h_y₂z₁ : R y₂ z₁ := hE h_y₁y₂ h2
  exact hE h_y₂z₁ h4

/-- C₁ is R-closed: if z ∈ C₁ and R(z, u), then u ∈ C₁. -/
lemma euclid_cluster_closed' {α : Type*} {R : α → α → Prop}
    (hE : Euclidean R) {w₀ y z u : α}
    (h1 : R w₀ y) (h2 : R y z) (h3 : R z u) :
    ∃ y', R w₀ y' ∧ R y' u := by
  have h_yy : R y y := euclid_succ_refl' hE h1
  have h_zy : R z y := hE h2 h_yy
  have h_yu : R y u := hE h_zy h3
  exact ⟨y, h1, h_yu⟩

/-- Any successor of a P-element is in C₁. Here P(w) means
    w = w₀ ∨ ∃ y, R(w₀, y) ∧ R(y, w). -/
lemma euclid_succ_in_cluster' {α : Type*} {R : α → α → Prop}
    (hE : Euclidean R) {w₀ w u : α}
    (hP : w = w₀ ∨ ∃ y, R w₀ y ∧ R y w) (hR : R w u) :
    ∃ y, R w₀ y ∧ R y u := by
  cases hP with
  | inl h =>
    subst h
    exact ⟨u, hR, euclid_succ_refl' hE hR⟩
  | inr h =>
    obtain ⟨y, hy₁, hy₂⟩ := h
    exact euclid_cluster_closed' hE hy₁ hy₂ hR

/-!
## § 2. Generated Subframe for Euclidean Frames
-/

/-- The Euclidean reachable set is R-closed. -/
lemma euclidReachable_closed' (F : Frame) (w₀ : F.states)
    (hE : Euclidean F.rel)
    {x y : F.states}
    (hx : x = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y x) (hxy : F.rel x y) :
    y = w₀ ∨ ∃ z, F.rel w₀ z ∧ F.rel z y :=
  Or.inr (euclid_succ_in_cluster' hE hx hxy)

/-!
## § 3. Filtration of the Euclidean Subframe Preserves Euclidean

The key theorem: the smallest filtration of the Euclidean generated subframe
is Euclidean. The proof uses the cluster property of C₁.
-/

/-
Key structural lemma: in the Euclidean subframe, any successor is
    in the cluster C₁, and C₁ elements are pairwise related. Therefore,
    the smallest filtration preserves the Euclidean property.

    Proof: Given [a] R_s [b] and [a] R_s [c], we extract witnesses
    a₁, b₁ with R(a₁, b₁) and a₂, c₁ with R(a₂, c₁). Since a₁ and a₂
    are in P (the reachable set), b₁ and c₁ lie in C₁. The cluster
    property gives R(b₁, c₁), hence [b] R_s [c].
-/
theorem euclidSubframe_filtration_euclidean (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) (w₀ : F.states) (hE : Euclidean F.rel) :
    let P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w
    let F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
    let v_sub := fun n (x : F_sub.states) => v n x.1
    Euclidean (filtrationFrame F_sub v_sub φ).rel := by
  simp_all +decide [ Euclidean ];
  rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ ⟨ z, hz ⟩ ⟨ a, b, ha, hb, hab ⟩ ⟨ c, d, hc, hd, hcd ⟩;
  refine' ⟨ b, d, hb, hd, _ ⟩;
  grind

/-!
## § 4. Validity and Satisfiability Definitions
-/

/-- **K5-validity**: φ is valid in all Euclidean frames. -/
def k5Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), Euclidean F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- **KD5-validity**: φ is valid in all serial-Euclidean frames. -/
def kd5Valid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}), BasicModal.Serial F.rel → Euclidean F.rel →
    ∀ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Satisfiability in Euclidean frames. -/
def euclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Finite satisfiability in Euclidean frames. -/
def finEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Satisfiability in serial-Euclidean frames. -/
def serialEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), BasicModal.Serial F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-- Finite satisfiability in serial-Euclidean frames. -/
def finSerialEuclidSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}), Finite F.states ∧ BasicModal.Serial F.rel ∧ Euclidean F.rel ∧
    ∃ (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 5. FMP for K5 and KD5
-/

/-- **FMP for K5**: Satisfiability in Euclidean frames implies finite
satisfiability in Euclidean frames. Uses the Euclidean generated subframe
followed by the smallest filtration. -/
theorem fmp_K5 (φ : Form) : euclidSatisfiable φ → finEuclidSatisfiable φ := by
  rintro ⟨F, hEuclid, v, w₀, hw₀⟩
  -- Step 1: Restrict to the Euclidean generated subframe
  set P := fun w => w = w₀ ∨ ∃ y, F.rel w₀ y ∧ F.rel y w with hP_def
  have hP_w₀ : P w₀ := Or.inl rfl
  have hP_closed : ∀ x y, P x → F.rel x y → P y := fun x y hx hxy =>
    euclidReachable_closed' F w₀ hEuclid hx hxy
  set F_sub : Frame := ⟨Subtype P, fun x y => F.rel x.1 y.1⟩
  set v_sub := fun n (x : F_sub.states) => v n x.1
  have hforces_sub : forces F_sub v_sub ⟨w₀, hP_w₀⟩ φ :=
    (forces_subtype hP_w₀ hP_closed).mp hw₀
  -- Step 2: Apply the smallest filtration to the subframe
  set filtF := filtrationFrame F_sub v_sub φ
  have hfilt_forces := (filtration_lemma F_sub v_sub φ ⟨w₀, hP_w₀⟩ φ
    (mem_subformulas_self φ)).mp hforces_sub
  -- Step 3: The filtration is finite and Euclidean
  exact ⟨filtF, inferInstance,
    euclidSubframe_filtration_euclidean F v φ w₀ hEuclid,
    filtrationVal F_sub v_sub φ, ⟦⟨w₀, hP_w₀⟩⟧, hfilt_forces⟩

/-- **FMP for KD5**: Satisfiability in serial-Euclidean frames implies
finite satisfiability in serial-Euclidean frames. -/
theorem fmp_KD5 (φ : Form) : serialEuclidSatisfiable φ → finSerialEuclidSatisfiable φ := by
  rintro ⟨F, hSerial, hEuclid, v, w₀, hw₀⟩
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
    euclidSubframe_filtration_euclidean F v φ w₀ hEuclid,
    filtrationVal F_sub v_sub φ, ⟦⟨w₀, hP_w₀⟩⟧, hfilt_forces⟩

/-!
## § 6. Validity ↔ Unsatisfiability
-/

theorem k5Valid_iff (φ : Form) : k5Valid φ ↔ ¬ euclidSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hE, v, w, hw⟩; exact hw (h F hE v w)
  · intro h F hE v w; by_contra hc; exact h ⟨F, hE, v, w, hc⟩

theorem kd5Valid_iff (φ : Form) : kd5Valid φ ↔ ¬ serialEuclidSatisfiable (∼φ) := by
  constructor
  · rintro h ⟨F, hS, hE, v, w, hw⟩; exact hw (h F hS hE v w)
  · intro h F hS hE v w; by_contra hc; exact h ⟨F, hS, hE, v, w, hc⟩

/-!
## § 7. Transfer to Fin n Preserving Frame Conditions
-/

def finNEuclidSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), Euclidean rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

def finNSerialEuclidSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop), BasicModal.Serial rel ∧ Euclidean rel ∧
    ∃ (v : Nat → Fin n → Prop) (w : Fin n), forces ⟨Fin n, rel⟩ v w φ

/-
Transfer to Fin n preserving Euclidean.
-/
lemma finite_model_to_fin_euclid {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hEuclid : Euclidean F.rel) (h : forces F v w φ) :
    finNEuclidSatisfiable φ (Fintype.card F.states) := by
  obtain ⟨e, he⟩ : ∃ (e : F.states ≃ Fin (Fintype.card F.states)), Function.Bijective e := ⟨ Fintype.equivFin F.states, Fintype.equivFin F.states |>.bijective ⟩;
  use fun i j => F.rel (e.symm i) (e.symm j);
  refine' ⟨ _, fun n i => v n ( e.symm i ), e w, _ ⟩;
  · exact fun i j k hij hjk => hEuclid hij hjk;
  · convert forces_equiv e _ _ _ _ |>.1 h;
    · aesop;
    · aesop

/-
Transfer to Fin n preserving serial + Euclidean.
-/
lemma finite_model_to_fin_serial_euclid {F : Frame} [Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (hSerial : BasicModal.Serial F.rel) (hEuclid : Euclidean F.rel)
    (h : forces F v w φ) :
    finNSerialEuclidSatisfiable φ (Fintype.card F.states) := by
  obtain ⟨e, he⟩ : ∃ e : F.states ≃ Fin (Fintype.card F.states), Function.Bijective e := by
    exact ⟨ Fintype.equivFin F.states, Fintype.equivFin F.states |>.bijective ⟩;
  refine' ⟨ fun i j => F.rel ( e.symm i ) ( e.symm j ), _, _, _ ⟩;
  · intro i; obtain ⟨ j, hj ⟩ := hSerial ( e.symm i ) ; use e j; aesop;
  · exact fun i j k hij hjk => hEuclid hij hjk;
  · use fun n i => v n (e.symm i), e w;
    convert forces_equiv e _ _ _ _ |>.1 h;
    · aesop;
    · aesop

/-!
## § 8. Bounded Satisfiability
-/

def boundedEuclidSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNEuclidSatisfiable φ n

def boundedSerialEuclidSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSerialEuclidSatisfiable φ n

/-!
## § 9. FMP Implies Bounded Satisfiability

These proofs inline the FMP construction to maintain the cardinality bound.
-/

theorem euclidSatisfiable_implies_bounded (φ : Form) :
    euclidSatisfiable φ → boundedEuclidSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hEuclid, v, w₀, hw₀⟩
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
    finite_model_to_fin_euclid
      (euclidSubframe_filtration_euclidean F v φ w₀ hEuclid)
      hfilt_forces⟩

theorem serialEuclidSatisfiable_implies_bounded (φ : Form) :
    serialEuclidSatisfiable φ →
    boundedSerialEuclidSatisfiable φ (2 ^ (subformulas φ).length) := by
  rintro ⟨F, hSerial, hEuclid, v, w₀, hw₀⟩
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
    finite_model_to_fin_serial_euclid
      (filtration_preserves_seriality F_sub v_sub φ hSub_serial)
      (euclidSubframe_filtration_euclidean F v φ w₀ hEuclid)
      hfilt_forces⟩

/-!
## § 10. Decidability of Bounded Satisfiability
-/

noncomputable instance decidable_finNEuclidSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNEuclidSatisfiable φ n) := by
  unfold finNEuclidSatisfiable; exact Classical.dec _

noncomputable instance decidable_finNSerialEuclidSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSerialEuclidSatisfiable φ n) := by
  unfold finNSerialEuclidSatisfiable; exact Classical.dec _

noncomputable instance decidable_boundedEuclidSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedEuclidSatisfiable φ N) := by
  unfold boundedEuclidSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNEuclidSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNEuclidSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

noncomputable instance decidable_boundedSerialEuclidSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSerialEuclidSatisfiable φ N) := by
  unfold boundedSerialEuclidSatisfiable
  rw [show (∃ n, n ≤ N ∧ finNSerialEuclidSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSerialEuclidSatisfiable φ k.val from by
    constructor
    · rintro ⟨n, hn, hsat⟩; exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩; exact ⟨n, by omega, hsat⟩]
  exact inferInstance

/-!
## § 11. Main Equivalences: Validity ↔ No Bounded Countermodel
-/

theorem k5Valid_iff_no_bounded_countermodel (φ : Form) :
    k5Valid φ ↔ ¬ boundedEuclidSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [k5Valid_iff]
  constructor
  · intro h hsat
    have : euclidSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (euclidSatisfiable_implies_bounded (∼φ) hsat)

theorem kd5Valid_iff_no_bounded_countermodel (φ : Form) :
    kd5Valid φ ↔ ¬ boundedSerialEuclidSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
  rw [kd5Valid_iff]
  constructor
  · intro h hsat
    have : serialEuclidSatisfiable (∼φ) :=
      match hsat with | ⟨n, _, rel, _, _, v, w, hw⟩ => ⟨⟨Fin n, rel⟩, ‹_›, ‹_›, v, w, hw⟩
    exact h this
  · intro h hsat
    exact h (serialEuclidSatisfiable_implies_bounded (∼φ) hsat)

/-!
## § 12. Decidability
-/

noncomputable instance decidable_k5Valid : DecidablePred k5Valid := by
  intro φ; rw [k5Valid_iff_no_bounded_countermodel]; exact inferInstance

noncomputable instance decidable_kd5Valid : DecidablePred kd5Valid := by
  intro φ; rw [kd5Valid_iff_no_bounded_countermodel]; exact inferInstance

end Modal