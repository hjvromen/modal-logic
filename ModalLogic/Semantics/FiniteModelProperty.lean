/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Finite Model Property for K

This file proves that the basic modal logic K has the **finite model property (FMP)**:
if a formula φ is satisfiable (true at some world in some model), then it is satisfiable
in a *finite* model (a model with finitely many worlds).

## Method: Filtration

We use the **filtration method**, which is the standard technique for establishing the FMP.

### Outline

Given a formula φ and a model (F, v) with a world w₀ where φ holds:

1. **Subformula closure**: Let Σ = subformulas(φ), a finite set.
2. **Equivalence relation**: Define x ∼ y iff for all ψ ∈ Σ,
   `forces F v x ψ ↔ forces F v y ψ` (x and y agree on all subformulas).
3. **Finite quotient**: The equivalence classes form a finite set
   (at most 2^|Σ| classes, since each class is determined by a truth assignment
   to Σ).
4. **Filtration frame**: Define the "smallest filtration" on equivalence classes:
   [x] R_f [y] iff there exist x' ∈ [x], y' ∈ [y] with F.rel x' y'.
5. **Truth preservation** (Filtration Lemma): For all ψ ∈ Σ and all worlds x,
   `forces F v x ψ ↔ forces F_f v_f [x] ψ`.
6. **Conclusion**: φ holds at [w₀] in the finite filtration model.

### Bound

The filtration model has at most 2^|Σ| worlds, where |Σ| is the number of
subformulas of φ. Since |Σ| ≤ complexity(φ), this gives an effective bound.

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §2.3
- Hughes & Cresswell, *A New Introduction to Modal Logic*, Ch. 6
-/

import Mathlib
import ModalLogic.Semantics.Soundness

namespace Modal
open Modal
open BasicModal

/-!
## § 1. Satisfiability
-/

/--
**Satisfiability**: A formula φ is satisfiable if there exists a frame, valuation,
and world where φ is true.
-/
def satisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}) (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/--
**Finite satisfiability**: A formula φ is finitely satisfiable if there exists
a *finite* frame, valuation, and world where φ is true.
-/
def finSatisfiable (φ : Form) : Prop :=
  ∃ (F : Frame.{0}) (_ : Finite F.states) (v : Nat → F.states → Prop) (w : F.states),
    forces F v w φ

/-!
## § 2. Subformula-Equivalence and Filtration
-/

/--
**Subformula equivalence**: Two worlds are equivalent with respect to a formula φ
if they agree on the truth value of every subformula of φ.

This is the key equivalence relation used in the filtration construction.
-/
def subfmlEquiv (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x y : F.states) : Prop :=
  ∀ ψ ∈ subformulas φ, (forces F v x ψ ↔ forces F v y ψ)

/--
Subformula equivalence is reflexive.
-/
lemma subfmlEquiv_refl {F : Frame} {v : Nat → F.states → Prop} {φ : Form}
    (x : F.states) : subfmlEquiv F v φ x x := by
  intro ψ _; exact Iff.rfl

/--
Subformula equivalence is symmetric.
-/
lemma subfmlEquiv_symm {F : Frame} {v : Nat → F.states → Prop} {φ : Form}
    {x y : F.states} (h : subfmlEquiv F v φ x y) : subfmlEquiv F v φ y x := by
  intro ψ hψ; exact (h ψ hψ).symm

/--
Subformula equivalence is transitive.
-/
lemma subfmlEquiv_trans {F : Frame} {v : Nat → F.states → Prop} {φ : Form}
    {x y z : F.states} (hxy : subfmlEquiv F v φ x y) (hyz : subfmlEquiv F v φ y z) :
    subfmlEquiv F v φ x z := by
  intro ψ hψ; exact (hxy ψ hψ).trans (hyz ψ hψ)

/--
Subformula equivalence is an equivalence relation.
-/
lemma subfmlEquiv_equivalence (F : Frame) (v : Nat → F.states → Prop) (φ : Form) :
    Equivalence (subfmlEquiv F v φ) :=
  ⟨fun x => subfmlEquiv_refl x, fun h => subfmlEquiv_symm h, fun h1 h2 => subfmlEquiv_trans h1 h2⟩

/--
The setoid induced by subformula equivalence.
-/
noncomputable def subfmlSetoid (F : Frame) (v : Nat → F.states → Prop) (φ : Form) :
    Setoid F.states where
  r := subfmlEquiv F v φ
  iseqv := subfmlEquiv_equivalence F v φ

/--
**Truth type**: The function that records which subformulas hold at a given world.
Two worlds are subformula-equivalent iff they have the same truth type.

We encode this as a function from the subformula list to Prop.
-/
noncomputable def truthType (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x : F.states) : List Form → Prop :=
  fun subs => ∀ ψ ∈ subs, forces F v x ψ

/-!
## § 3. The Filtration Frame
-/

/--
**Filtration frame**: Given a model (F, v) and a formula φ, the filtration
frame has:
- States: equivalence classes of worlds under subformula equivalence
- Relation: [x] R [y] iff ∃ x' ∈ [x], y' ∈ [y] with F.rel x' y'

This is the "smallest filtration" (also called the coarsest filtration).
-/
noncomputable def filtrationFrame (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Frame where
  states := Quotient (subfmlSetoid F v φ)
  rel := Quotient.lift₂
    (fun x y => ∃ x' y', subfmlEquiv F v φ x x' ∧ subfmlEquiv F v φ y y' ∧ F.rel x' y')
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      simp only [eq_iff_iff]
      constructor
      · rintro ⟨x', y', hax, hby, hrel⟩
        exact ⟨x', y', subfmlEquiv_trans (subfmlEquiv_symm ha) hax,
               subfmlEquiv_trans (subfmlEquiv_symm hb) hby, hrel⟩
      · rintro ⟨x', y', hax, hby, hrel⟩
        exact ⟨x', y', subfmlEquiv_trans ha hax, subfmlEquiv_trans hb hby, hrel⟩)

/--
**Filtration valuation**: Variable n holds at equivalence class [x] iff
it holds at x. This is well-defined for variables that appear as subformulas
of φ (subformula equivalence preserves their truth). For variables not appearing
as subformulas, we set them to `False` — this doesn't affect the filtration
lemma since those variables don't occur in subformulas of φ.
-/
noncomputable def filtrationVal (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Nat → (filtrationFrame F v φ).states → Prop :=
  fun n q =>
    if hmem : Form.var n ∈ subformulas φ then
      Quotient.lift (fun x => v n x)
        (by
          intro a b hab
          simp only [eq_iff_iff]
          exact hab (Form.var n) hmem)
        q
    else
      False

/-!
## § 4. Filtration Lemma (Truth Preservation)
-/

/-- If □ψ ∈ subformulas φ, then ψ ∈ subformulas φ. By induction on φ. -/
lemma box_subformula_imp_subformula {φ ψ : Form} :
    Form.box ψ ∈ subformulas φ → ψ ∈ subformulas φ := by
  have h_pos : ∀ φ, ∀ ψ, Form.box ψ ∈ subformulas φ → ψ ∈ subformulas φ := by
    intro φ ψ hψ;
    induction' φ with φ ψ hψ φ ψ hψ hψ' φ hψ hψ' hψ'' ψ hψ hψ' hψ'' <;> simp_all +decide [ subformulas ];
    · grind +splitImp;
    · grind +qlia;
    · cases hψ <;> simp_all +decide [ subformulas ];
      exact Or.inr ( mem_subformulas_self _ );
  exact h_pos φ ψ

/-- If ψ₁ & ψ₂ ∈ subformulas φ, then ψ₁ ∈ subformulas φ. By induction on φ. -/
lemma and_subformula_left {φ ψ₁ ψ₂ : Form} :
    Form.and ψ₁ ψ₂ ∈ subformulas φ → ψ₁ ∈ subformulas φ := by
  induction' φ with _ _ _ _ _ φ₁ φ₂ ih₁ ih₂ φ' ih' <;> simp_all +decide [ subformulas ];
  · grind +suggestions;
  · grind +ring

/-- If ψ₁ & ψ₂ ∈ subformulas φ, then ψ₂ ∈ subformulas φ. By induction on φ. -/
lemma and_subformula_right {φ ψ₁ ψ₂ : Form} :
    Form.and ψ₁ ψ₂ ∈ subformulas φ → ψ₂ ∈ subformulas φ := by
  -- By definition of subformulas, if ψ₁ ⋏ ψ₂ is in the subformulas of φ, then both ψ₁ and ψ₂ must be in the subformulas of φ.
  intro h_sub
  have h_and : ψ₁ ⋏ ψ₂ ∈ subformulas φ := h_sub
  have h_ψ₂ : ψ₂ ∈ subformulas φ := by
    revert h_and φ; (
    -- By definition of subformulas, if ψ₁ ⋏ ψ₂ is in the subformulas of φ, then ψ₂ must be in the subformulas of φ.
    intros φ h_sub
    induction' φ with φ ψ₁ ψ₂ ih₁ ih₂ generalizing ψ₁ ψ₂ <;> simp_all +decide [ subformulas ];
    · grind +suggestions;
    · grind +ring;
    · grind);
  exact h_ψ₂

/-- If ψ₁ ⊃ ψ₂ ∈ subformulas φ, then ψ₁ ∈ subformulas φ. By induction on φ. -/
lemma impl_subformula_left {φ ψ₁ ψ₂ : Form} :
    Form.impl ψ₁ ψ₂ ∈ subformulas φ → ψ₁ ∈ subformulas φ := by
  intro h; induction φ <;> simp_all +decide [ subformulas ] ;
  · grind +ring;
  · grind +suggestions

/-- If ψ₁ ⊃ ψ₂ ∈ subformulas φ, then ψ₂ ∈ subformulas φ. By induction on φ. -/
lemma impl_subformula_right {φ ψ₁ ψ₂ : Form} :
    Form.impl ψ₁ ψ₂ ∈ subformulas φ → ψ₂ ∈ subformulas φ := by
  induction φ <;> simp_all +decide only [subformulas];
  · aesop;
  · aesop;
  · aesop;
  · grind +suggestions;
  · aesop

/--
**Filtration Lemma**: For any subformula ψ of φ, truth in the original model
is equivalent to truth in the filtration model. By induction on ψ.

- **Box case (→)**: If `[x] R_f [y]`, there exist `x' ∼ x`, `y' ∼ y` with
  `F.rel x' y'`. Subformula equivalence transfers `□ψ'` from `x` to `x'`,
  then `F.rel x' y'` gives `ψ'` at `y'`, and equivalence transfers back to `y`.
- **Box case (←)**: Given `F.rel x y`, reflexive equivalences give `[x] R_f [y]`,
  then the IH transfers back.
-/
theorem filtration_lemma (F : Frame) (v : Nat → F.states → Prop) (φ : Form)
    (x : F.states) (ψ : Form) (hψ : ψ ∈ subformulas φ) :
    forces F v x ψ ↔
      forces (filtrationFrame F v φ) (filtrationVal F v φ)
        (Quotient.mk (subfmlSetoid F v φ) x) ψ := by
  induction' ψ with ψ₁ ψ₂ hψ₁ hψ₂ generalizing x;
  · bound;
  · unfold forces filtrationVal; aesop;
  · have := and_subformula_left hψ; have := and_subformula_right hψ; aesop;
  · rw [ forces_impl, forces_impl ];
    rw [ ‹∀ x : F.states, _ ∈ subformulas φ → ( forces F v x _ ↔ forces ( filtrationFrame F v φ ) ( filtrationVal F v φ ) ⟦x⟧ _ ) › x ( impl_subformula_left hψ ), ‹∀ x : F.states, _ ∈ subformulas φ → ( forces F v x _ ↔ forces ( filtrationFrame F v φ ) ( filtrationVal F v φ ) ⟦x⟧ _ ) › x ( impl_subformula_right hψ ) ];
  · rename_i h₁ h₂;
    constructor <;> intro h;
    · intro q hq;
      obtain ⟨ y, hy ⟩ := Quotient.exists_rep q;
      -- By definition of filtrationFrame, we know that there exist x' and y' such that x~x', y~y', and F.rel x' y'.
      obtain ⟨x', y', hx', hy', hxy'⟩ : ∃ x' y', subfmlEquiv F v φ x x' ∧ subfmlEquiv F v φ y y' ∧ F.rel x' y' := by
        unfold filtrationFrame at hq; aesop;
      have h_forces_y' : forces F v y' h₁ := by
        have h_forces_y' : forces F v x' (□ h₁) := by
          exact hx' _ hψ |>.1 h;
        exact h_forces_y' y' hxy';
      have h_forces_y : forces F v y h₁ := by
        exact hy' _ ( box_subformula_imp_subformula hψ ) |>.2 h_forces_y';
      exact hy ▸ h₂ y ( by
        exact? ) |>.1 h_forces_y;
    · intro y hy; have := h; simp_all +decide [ forces ] ;
      contrapose! h;
      refine' ⟨ ⟦y⟧, _, _ ⟩ <;> simp_all +decide [ filtrationFrame ];
      · exact ⟨ x, subfmlEquiv_refl _, y, subfmlEquiv_refl _, hy ⟩;
      · grind +suggestions

/-!
## § 5. Finiteness of the Filtration
-/

/--
**Finiteness of filtration**: The quotient has at most 2^|Sub(φ)| equivalence
classes, since each class is determined by a truth assignment to the finite set
of subformulas. We inject equivalence classes into `Sub(φ) → Prop` and use
classical finiteness.
-/
noncomputable instance filtration_finite (F : Frame) (v : Nat → F.states → Prop)
    (φ : Form) : Finite (filtrationFrame F v φ).states := by
  -- Let's denote the finite set of subformulas of φ by S.
  set S := subformulas φ with hS_def;
  have h_finite : Finite (Set.range (fun x => fun ψ : S.toFinset => forces F v x ψ)) := by
    exact Set.toFinite _;
  refine' h_finite.of_injective _ _;
  exact fun q => ⟨ _, ⟨ q.out, rfl ⟩ ⟩;
  intro q₁ q₂ h_eq; simp_all +decide [ funext_iff, Quotient.eq ] ;
  rw [ ← Quotient.out_eq q₁, ← Quotient.out_eq q₂ ];
  exact Quotient.sound fun ψ hψ => by specialize h_eq ψ; aesop;

/-!
## § 6. The Finite Model Property
-/

/--
**Finite Model Property for K**: If φ is satisfiable, then it is satisfiable in
a finite model. Construct the filtration, apply the filtration lemma, and use
finiteness of the quotient.
-/
theorem finite_model_property (φ : Form) :
    satisfiable φ → finSatisfiable φ := by
  intro h
  obtain ⟨F, v, w, hw⟩ := h;
  use filtrationFrame F v φ, by
    exact?, filtrationVal F v φ, Quotient.mk (subfmlSetoid F v φ) w;
  generalize_proofs at *;
  convert filtration_lemma F v φ w φ ( mem_subformulas_self φ ) |>.1 hw using 1

end Modal