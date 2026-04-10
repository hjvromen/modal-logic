/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Frame Correspondence Theory: Predicate-Level

This file defines predicate-level modal operators and proves correspondence theorems
relating frame conditions to modal axiom schemata.

## Syntactic Definability

Syntactic definability results (frame class definitions, the `Defines` predicate, and
definability theorems for T/B/4/5/D) live in `Definability.lean` in the `BasicModal`
namespace. Those definitions are the canonical source of truth for frame classes such as
`refClass`, `symmClass`, `transClass`, `euclidClass`, `serialClass`, and their
combinations. Downstream files should use `open BasicModal` to access them.

## Predicate-Level Correspondence

This file defines modal operators (□, ⬦) as operations on predicates
`f.states → Prop`, together with frame property definitions and correspondence
theorems relating frame conditions to modal axiom schemata:

| Frame property | Axiom schema | Name |
|---------------|-------------|------|
| Reflexive | □φ → φ | T |
| Symmetric | φ → □⬦φ | B |
| Transitive | □φ → □□φ | 4 |
| Euclidean | ⬦φ → □⬦φ | 5 |
| Serial | □φ → ⬦φ | D |
| Confluent | ⬦□φ → □⬦φ | BDDB |
| Trans + CWF | □(□φ→φ) → □φ | GL |

Also includes system characterizations (S4, S5, KD45, GL).
-/

import ModalLogic.Semantics.Definability
import Mathlib.Tactic

/-! ## Predicate-Level Modal Operators and Correspondence Theory

This section defines modal operators (□, ⬦) and logical connectives as operations
on predicates `f.states → Prop`, and proves correspondence theorems relating
frame conditions to modal axiom schemata.

These definitions and results are used by the epistemic logic modules for
semantic reasoning about common knowledge, distributed knowledge, etc.
-/

namespace Modal
namespace Frame
variable {f : Frame}

/-! ### Propositional semantics over a frame

We interpret modal formulas as predicates on worlds. The modal operators
□ (box, necessity) and ⬦ (diamond, possibility) quantify over accessible worlds.
-/

/-- Pointwise negation of a formula (as a predicate on worlds). -/
def neg (φ : f.states → Prop) : f.states → Prop := fun w => ¬ φ w

/-- Pointwise conjunction of formulas. -/
def conj (φ ψ : f.states → Prop) : f.states → Prop := fun w => φ w ∧ ψ w

/-- Box (necessity) modality: □φ holds at w if φ holds at all accessible worlds. -/
def box (φ : f.states → Prop) : f.states → Prop :=
  fun w => ∀ v, f.rel w v → φ v

/-- Diamond (possibility) modality: ⬦φ holds at w if φ holds at some accessible world. -/
def diamond (φ : f.states → Prop) : f.states → Prop :=
  fun w => ∃ v, f.rel w v ∧ φ v

/-- Material implication between formulas. -/
def impl (φ ψ : f.states → Prop) : f.states → Prop :=
  fun w => φ w → ψ w

/-- Validity of a formula: true at every world. -/
def valid (φ : f.states → Prop) : Prop := ∀ w, φ w

/-- Operator notations (scoped to `Modal.Frame` to avoid conflicts with
    syntactic `□` from the Syntax module). -/
scoped prefix:90  "¬ₘ " => neg
scoped infixr:35  " ∧ₘ " => conj
scoped prefix:80  "□ "   => box
scoped prefix:80  "⬦ "   => diamond
scoped infixr:55  " ⟶ "  => impl
scoped prefix:40  "⊢ "   => valid

@[simp] lemma neg_def {φ : f.states → Prop} : neg φ = fun w => ¬ φ w := rfl
@[simp] lemma conj_def {φ ψ : f.states → Prop} : conj φ ψ = fun w => φ w ∧ ψ w := rfl
@[simp] lemma box_def {φ : f.states → Prop} : box φ = fun w => ∀ v, f.rel w v → φ v := rfl
@[simp] lemma diamond_def {φ : f.states → Prop} : diamond φ = fun w => ∃ v, f.rel w v ∧ φ v := rfl
@[simp] lemma impl_def {φ ψ : f.states → Prop} : impl φ ψ = fun w => φ w → ψ w := rfl


/-! ### Propositional tautologies -/

@[simp] lemma neg_neg₁ {φ : f.states → Prop} : neg (neg φ) = φ := by
  funext w; simp [neg_def]

/-! ### Dualities between □ and ⬦

To avoid `simp` loops, we register only **one** direction as a simp-lemma:
`¬ₘ (□ φ) = ⬦ (¬ₘ φ)`. The other directions are ordinary lemmas for use with `rw`.
-/

@[simp] lemma not_box_diamond_not {φ : f.states → Prop} : neg (box φ) = diamond (neg φ) := by
  funext w; simp [neg_def, box_def, diamond_def]

lemma not_diamond_box_not {φ : f.states → Prop} : neg (⬦ φ) = □ (neg φ) := by
  funext w; simp [neg_def, box_def, diamond_def]

lemma box_from_diamond {φ : f.states → Prop} : □ φ = neg (⬦ (neg φ)) := by
  funext w; simp [neg_def, box_def, diamond_def]

@[simp]
lemma diamond_from_box {φ : f.states → Prop} : ⬦ φ = neg (□ (neg φ)) := by
  funext w
  apply propext
  constructor
  · rintro ⟨v, hwv, hv⟩ hBox
    exact (hBox v hwv) hv
  · intro hn
    by_contra h'
    have all_neg : ∀ v, f.rel w v → ¬ φ v := by
      intro v hr hφv
      exact h' ⟨v, hr, hφv⟩
    exact hn all_neg

/-! ### Basic proof principles -/

/-- Necessitation: validity lifts under □. If φ is valid, then □φ is valid. -/
lemma Nec {φ : f.states → Prop} : (⊢ φ) → (⊢ □ φ) := by
  intro h w v _; exact h v

/-- K axiom schema: □(φ → ψ) → (□φ → □ψ) is valid on all frames. -/
lemma K {φ ψ : f.states → Prop} : ⊢ (□ (φ ⟶ ψ) ⟶ (□ φ ⟶ □ ψ)) := by
  intro w hImp hBoxφ v hv; exact hImp v hv (hBoxφ v hv)

/-! ### Distribution over conjunction -/

/-- M: □(φ ∧ ψ) → (□φ ∧ □ψ). -/
lemma M {φ ψ : f.states → Prop} : ⊢ (□ (φ ∧ₘ ψ) ⟶ (□ φ ∧ₘ □ ψ)) := by
  intro w h
  exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩

/-- C: (□φ ∧ □ψ) → □(φ ∧ ψ). -/
lemma C {φ ψ : f.states → Prop} : ⊢ ((□ φ ∧ₘ □ ψ) ⟶ □ (φ ∧ₘ ψ)) := by
  intro w h v hv; exact ⟨h.1 v hv, h.2 v hv⟩

/-! ### Frame properties -/

/-- A frame is reflexive if every world accesses itself. -/
def Reflexive (f : Frame) : Prop := ∀ w : f.states, f.rel w w
/-- A frame is symmetric if accessibility is bidirectional. -/
def Symmetric (f : Frame) : Prop := ∀ {w v : f.states}, f.rel w v → f.rel v w
/-- A frame is transitive if accessibility chains compose. -/
def Transitive (f : Frame) : Prop := ∀ {u v w : f.states}, f.rel u v → f.rel v w → f.rel u w
/-- A frame is serial if every world has at least one successor. -/
def Serial (f : Frame) : Prop := ∀ w : f.states, ∃ v, f.rel w v
/-- A frame is Euclidean if R(x,y) ∧ R(x,z) → R(y,z). -/
def Euclidean (f : Frame) : Prop := ∀ {x y z : f.states}, f.rel x y → f.rel x z → f.rel y z
/-- A frame is confluent (Church–Rosser). -/
def Confluence (f : Frame) : Prop := ∀ a b c, f.rel a b ∧ f.rel a c → ∃ d, f.rel b d ∧ f.rel c d
/-- The converse of the accessibility relation is well-founded. -/
def Converse_wellfounded (f : Frame) : Prop := WellFounded (flip f.rel)
/-- Transitive and conversely well-founded (characterizes GL frames). -/
def Trans_cv_wf (f : Frame) : Prop := Transitive f ∧ Converse_wellfounded f

/-! ### Axiom schemata as frame properties -/

def T (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (□ φ ⟶ φ)
def B (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (φ ⟶ □ ⬦ φ)
def D (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (□ φ ⟶ ⬦ φ)
def IV (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (□ φ ⟶ □ (□ φ))
def V (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (⬦ φ ⟶ □ (⬦ φ))
def BDDB (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (⬦ (□ φ) ⟶ □ (⬦ φ))

/-! ### Correspondence: T ↔ Reflexive -/

lemma T_of_Reflexive (hR : Reflexive f) : T f := by
  intro φ w hBox; exact hBox w (hR w)

lemma Reflexive_of_T (hT : T f) : Reflexive f := by
  intro w
  have h := hT (fun v => f.rel w v) w
  exact h (fun v hv => hv)

theorem T_iff_Reflexive : T f ↔ Reflexive f :=
  ⟨Reflexive_of_T, T_of_Reflexive⟩

/-! ### Correspondence: D ↔ Serial -/

lemma D_of_Serial (hS : Serial f) : D f := by
  intro φ w hBox
  obtain ⟨v, hwv⟩ := hS w
  exact ⟨v, hwv, hBox v hwv⟩

lemma Serial_of_D (hD : D f) : Serial f := by
  intro w
  have h := hD (fun _ => True) w (fun v _ => trivial)
  obtain ⟨v, hv, _⟩ := h; exact ⟨v, hv⟩

theorem D_iff_Serial : D f ↔ Serial f :=
  ⟨Serial_of_D, D_of_Serial⟩

/-! ### Correspondence: B ↔ Symmetric -/

lemma B_of_Symmetric (hS : Symmetric f) : B f := by
  intro φ w hφ v hv; exact ⟨w, hS hv, hφ⟩

lemma Symmetric_of_B (hB : B f) : Symmetric f := by
  intro w v hwv
  have h := hB (fun x => x = w) w rfl v hwv
  obtain ⟨u, hvu, rfl⟩ := h; exact hvu

theorem B_iff_Symmetric : B f ↔ Symmetric f :=
  ⟨Symmetric_of_B, B_of_Symmetric⟩

/-! ### Correspondence: 4 ↔ Transitive -/

lemma Four_of_Transitive (hTr : Transitive f) : IV f := by
  intro φ w h v hv u huv; exact h u (hTr hv huv)

lemma Transitive_of_Four (h4 : IV f) : Transitive f := by
  intro u v w huv hvw
  exact h4 (fun x => f.rel u x) u (fun x hux => hux) v huv w hvw

theorem Four_iff_Transitive : IV f ↔ Transitive f :=
  ⟨Transitive_of_Four, Four_of_Transitive⟩

/-! ### Correspondence: 5 ↔ Euclidean -/

lemma Five_of_Euclidean (hE : Euclidean f) : V f := by
  intro φ w h v hv
  obtain ⟨u, hwu, hφu⟩ := h
  exact ⟨u, hE hv hwu, hφu⟩

lemma Euclidean_of_Five (h5 : V f) : Euclidean f := by
  intro w u v hwu hwv
  have h := h5 (fun x => x = v) w ⟨v, hwv, rfl⟩ u hwu
  obtain ⟨t, hut, rfl⟩ := h; exact hut

theorem Five_iff_Euclidean : V f ↔ Euclidean f :=
  ⟨Euclidean_of_Five, Five_of_Euclidean⟩

/-! ### Correspondence: BDDB ↔ Confluence -/

lemma BDDB_of_Confluence (hC : Confluence f) : BDDB f := by
  intro φ w h u huw
  obtain ⟨v, hwv, hφv⟩ := h
  obtain ⟨d, hvd, hud⟩ := hC w v u ⟨hwv, huw⟩
  exact ⟨d, hud, hφv d hvd⟩

lemma Confluence_of_BDDB (hB : BDDB f) : Confluence f := by
  intro a b c ⟨hab, hac⟩
  have hbox : (□ (fun x => f.rel b x)) b := fun x hbx => hbx
  have hdia : (⬦ (□ (fun x => f.rel b x))) a := ⟨b, hab, hbox⟩
  obtain ⟨d, hcd, hφd⟩ := hB _ a hdia c hac
  exact ⟨d, hφd, hcd⟩

theorem BDDB_iff_Confluence : BDDB f ↔ Confluence f :=
  ⟨Confluence_of_BDDB, BDDB_of_Confluence⟩

/-! ### Modal system characterizations -/

/-- S4 frames are exactly reflexive and transitive frames. -/
theorem S4_char : T f ∧ IV f ↔ Reflexive f ∧ Transitive f := by
  constructor
  · intro ⟨hT, hIV⟩; exact ⟨Reflexive_of_T hT, Transitive_of_Four hIV⟩
  · intro ⟨hR, hTr⟩; exact ⟨T_of_Reflexive hR, Four_of_Transitive hTr⟩

/-- S5 frames are exactly equivalence relations. -/
theorem S5_char : T f ∧ IV f ∧ B f ↔ Reflexive f ∧ Transitive f ∧ Symmetric f := by
  constructor
  · intro ⟨hT, hIV, hB⟩
    exact ⟨Reflexive_of_T hT, Transitive_of_Four hIV, Symmetric_of_B hB⟩
  · intro ⟨hR, hTr, hS⟩
    exact ⟨T_of_Reflexive hR, Four_of_Transitive hTr, B_of_Symmetric hS⟩

/-- Alternative S5 characterization via Euclidean property. -/
theorem S5_char_euclidean : T f ∧ V f ↔ Reflexive f ∧ Euclidean f := by
  constructor
  · intro ⟨hT, hV⟩; exact ⟨Reflexive_of_T hT, Euclidean_of_Five hV⟩
  · intro ⟨hR, hE⟩; exact ⟨T_of_Reflexive hR, Five_of_Euclidean hE⟩

/-- KD45 frames are serial, transitive, and Euclidean. -/
theorem KD45_char : D f ∧ IV f ∧ V f ↔ Serial f ∧ Transitive f ∧ Euclidean f := by
  constructor
  · intro ⟨hD, hIV, hV⟩
    exact ⟨Serial_of_D hD, Transitive_of_Four hIV, Euclidean_of_Five hV⟩
  · intro ⟨hS, hTr, hE⟩
    exact ⟨D_of_Serial hS, Four_of_Transitive hTr, Five_of_Euclidean hE⟩

/-! ### Gödel–Löb logic GL

The GL schema □(□φ → φ) → □φ holds exactly on transitive, conversely well-founded
frames (no infinite ascending chains in the accessibility relation).
-/

def G_L (f : Frame) : Prop := ∀ φ : f.states → Prop, ⊢ (□ (□ φ ⟶ φ) ⟶ □ φ)

lemma G_L_of_Trans_cv_wf (htr : Transitive f) (hwf : Converse_wellfounded f) : G_L f := by
  intro φ w hPrem
  have main : (□ (impl (□ φ) φ)) w → (□ φ) w := by
    refine hwf.induction (C := fun x => (□ (impl (□ φ) φ)) x → (□ φ) x) w ?_
    intro x ih Hx y hxy
    have Hy : (□ (impl (□ φ) φ)) y := fun z hyz => Hx z (htr hxy hyz)
    have hBoxφy : (□ φ) y := ih y hxy Hy
    exact Hx y hxy hBoxφy
  exact main hPrem

private lemma transitive_of_GL (hGL : G_L f) : Transitive f := by
  intro a b c hab hbc
  by_contra hnot
  let ψ : f.states → Prop := fun x => x ≠ b ∧ x ≠ c
  have hPrem : (□ (impl (□ ψ) ψ)) a := by
    intro v hav
    by_cases hb : v = b
    · have hNotBoxV : ¬ (□ ψ) v := by
        intro hbox
        have hvc : f.rel v c := by simpa [hb] using hbc
        exact (hbox c hvc).2 rfl
      intro hboxv; exact (hNotBoxV hboxv).elim
    · have hvc : v ≠ c := fun hvceq => hnot (by simpa [hvceq] using hav)
      intro _; exact ⟨hb, hvc⟩
  have hNotBoxA : ¬ (□ ψ) a := by
    intro hbox; exact (hbox b hab).1 rfl
  exact hNotBoxA (hGL ψ a hPrem)

private lemma wf_flip_of_GL (hGL : G_L f) : WellFounded (flip f.rel) := by
  by_contra hnot
  have : ∃ x, ¬ Acc (flip f.rel) x := by
    by_contra hforall
    exact hnot ⟨fun x => by_contra fun hx => hforall ⟨x, hx⟩⟩
  obtain ⟨w0, hNotAcc0⟩ := this
  have succ_not_acc : ∀ x, ¬ Acc (flip f.rel) x → ∃ y, f.rel x y ∧ ¬ Acc (flip f.rel) y := by
    intro x hx
    by_contra hnone
    have allAccSucc : ∀ y, f.rel x y → Acc (flip f.rel) y := by
      intro y hxy; by_contra hy; exact hnone ⟨y, hxy, hy⟩
    exact hx (Acc.intro x fun y hy => allAccSucc y (by simpa [flip] using hy))
  obtain ⟨v1, hw0v1, hNotAcc1⟩ := succ_not_acc w0 hNotAcc0
  obtain ⟨_, _, _⟩ := succ_not_acc v1 hNotAcc1
  let φ : f.states → Prop := fun x => Acc (flip f.rel) x
  have hPrem : (□ (impl (□ φ) φ)) w0 := by
    intro v _
    by_cases hvAcc : Acc (flip f.rel) v
    · intro _; exact hvAcc
    · obtain ⟨u, hvu, hNotAccU⟩ := succ_not_acc v hvAcc
      intro hbox; exact (hNotAccU (hbox u hvu)).elim
  exact (fun hbox => hNotAcc1 (hbox v1 hw0v1)) (hGL φ w0 hPrem)

lemma Trans_cv_wf_of_GL (hGL : G_L f) : Trans_cv_wf f :=
  ⟨transitive_of_GL hGL, wf_flip_of_GL hGL⟩

/-- GL holds iff the frame is transitive and conversely well-founded. -/
theorem GL_iff_Trans_cv_wf : G_L f ↔ Trans_cv_wf f := by
  constructor
  · exact Trans_cv_wf_of_GL
  · intro ⟨htr, hwf⟩; exact G_L_of_Trans_cv_wf htr hwf

/-- GL implies positive introspection (axiom 4). -/
lemma IV_of_GL : G_L f → IV f := by
  intro hGL; exact Four_of_Transitive (Trans_cv_wf_of_GL hGL).1

/-! ### Example frames -/

/-- ℕ with ≤ is a reflexive, transitive frame (S4). -/
def nat_frame : Frame := ⟨ℕ, (· ≤ ·)⟩

example : Reflexive nat_frame := fun _ => Nat.le_refl _
example : Transitive nat_frame := fun h1 h2 => Nat.le_trans h1 h2

/-- ℕ with < is a transitive, conversely well-founded frame (GL). -/
def nat_strict_frame : Frame := ⟨ℕ, (· < ·)⟩

example : Transitive nat_strict_frame := fun h1 h2 => Nat.lt_trans h1 h2

/-- The universal frame (all worlds see all worlds) is S5. -/
def universal_frame (W : Type) : Frame := ⟨W, fun _ _ => True⟩

example (W : Type) : Reflexive (universal_frame W) := fun _ => trivial
example (W : Type) : Transitive (universal_frame W) := fun _ _ => trivial
example (W : Type) : Symmetric (universal_frame W) := fun _ => trivial

end Frame

end Modal
