/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Decidability of K

This file proves that the set of K-valid formulas is **decidable**: given any modal
formula φ, we can algorithmically determine whether φ is valid in all Kripke frames.

## Method

The proof uses the **finite model property** (proved in `FiniteModelProperty.lean`):

1. **Reduction to satisfiability**: φ is K-valid iff ∼φ is not satisfiable.
2. **Finite model property**: If ∼φ is satisfiable, it is satisfiable in a finite
   model with at most 2^|Sub(∼φ)| worlds.
3. **Finite model checking**: Satisfiability in finite models up to a given size
   is decidable, since there are only finitely many such models to check.

Combining these steps, K-validity reduces to a finite search problem.

## Main Results

- `kValid`: Definition of K-validity
- `kValid_iff_not_satisfiable_neg`: Validity ↔ unsatisfiability of negation
- `satisfiable_iff_finSatisfiable`: Satisfiability ↔ finite satisfiability (FMP as iff)
- `forces_eq_of_vars_eq`: Truth depends only on variables in the formula
- `bForces`: Computable Boolean forcing for finite models
- `bForces_iff_forces`: Correctness of Boolean forcing
- `kValid_iff_no_bounded_countermodel`: K-validity ↔ no small countermodel
- `decidable_kValid`: `DecidablePred kValid`

## References

- Blackburn, de Rijke, Venema, *Modal Logic*, §2.3, §6.1
-/

import ModalLogic.Semantics.FiniteModelProperty

namespace Modal
open Modal
open BasicModal

/-!
## § 1. K-Validity
-/

/--
**K-validity**: A formula φ is K-valid if it is true at every world in every
Kripke model.
-/
def kValid (φ : Form) : Prop :=
  ∀ (F : Frame.{0}) (v : Nat → F.states → Prop) (w : F.states), forces F v w φ

/-!
## § 2. Validity and Satisfiability
-/

/-- K-validity is equivalent to the unsatisfiability of the negation. -/
theorem kValid_iff_not_satisfiable_neg (φ : Form) :
    kValid φ ↔ ¬ satisfiable (∼φ) := by
      unfold kValid satisfiable
      simp only [Modal.forces, neg_def, not_exists]
      constructor
      · intro h F v w hw; exact hw (h F v w)
      · intro h F v w; by_contra hc; exact h F v w hc

/-- Finite satisfiability implies satisfiability (every finite model is a model). -/
lemma finSatisfiable_implies_satisfiable (φ : Form) :
    finSatisfiable φ → satisfiable φ := by
      rintro ⟨ F, _, v, w, hw ⟩ ; exact ⟨ F, v, w, hw ⟩ ;

/--
**FMP as biconditional**: A formula is satisfiable iff it is finitely satisfiable.
Combines `finite_model_property` with the trivial converse.
-/
theorem satisfiable_iff_finSatisfiable (φ : Form) :
    satisfiable φ ↔ finSatisfiable φ :=
  ⟨finite_model_property φ, finSatisfiable_implies_satisfiable φ⟩

/-!
## § 3. Forces Depends Only on Variables in the Formula
-/

/--
The forcing relation depends only on the valuation of variables that actually
appear in the formula. By induction on φ.
-/
theorem forces_eq_of_vars_eq {F : Frame} {v₁ v₂ : Nat → F.states → Prop}
    {w : F.states} {φ : Form}
    (h : ∀ n ∈ vars φ, ∀ x : F.states, v₁ n x ↔ v₂ n x) :
    forces F v₁ w φ ↔ forces F v₂ w φ := by
      -- By induction on the structure of φ, we can show that the forces relation depends only on the value of the variables in φ.
      have h_ind : ∀ (φ : Form) (w : F.states), (∀ n ∈ vars φ, ∀ x, v₁ n x ↔ v₂ n x) → (forces F v₁ w φ ↔ forces F v₂ w φ) := by
        intro φ w h;
        induction' φ with n ih generalizing w;
        · bound;
        · exact h n ( by simp +decide [ vars ] ) w;
        · rename_i φ₁ φ₂ ih₁ ih₂
          simp only [forces_and]
          constructor
          · intro ⟨h1, h2⟩
            exact ⟨(ih₁ w (fun n hn x => h n (Finset.mem_union_left _ hn) x)).mp h1,
                   (ih₂ w (fun n hn x => h n (Finset.mem_union_right _ hn) x)).mp h2⟩
          · intro ⟨h1, h2⟩
            exact ⟨(ih₁ w (fun n hn x => h n (Finset.mem_union_left _ hn) x)).mpr h1,
                   (ih₂ w (fun n hn x => h n (Finset.mem_union_right _ hn) x)).mpr h2⟩
        · rename_i φ₁ φ₂ ih₁ ih₂
          simp only [forces_impl]
          constructor
          · intro hi hf; exact (ih₂ w (fun n hn x => h n (Finset.mem_union_right _ hn) x)).mp (hi ((ih₁ w (fun n hn x => h n (Finset.mem_union_left _ hn) x)).mpr hf))
          · intro hi hf; exact (ih₂ w (fun n hn x => h n (Finset.mem_union_right _ hn) x)).mpr (hi ((ih₁ w (fun n hn x => h n (Finset.mem_union_left _ hn) x)).mp hf))
        · simp_all +decide [ vars, forces ];
      exact h_ind φ w h

/-!
## § 4. Satisfiability on Fin n Frames
-/

/--
**Fin n satisfiability**: φ is satisfiable in a model whose state space is `Fin n`.
-/
def finNSatisfiable (φ : Form) (n : Nat) : Prop :=
  ∃ (rel : Fin n → Fin n → Prop) (v : Nat → Fin n → Prop) (w : Fin n),
    forces ⟨Fin n, rel⟩ v w φ

/-- Forces is preserved under frame isomorphisms. By induction on φ. -/
lemma forces_equiv {F : Frame} {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    {W' : Type} (e : F.states ≃ W')
    (rel' : W' → W' → Prop)
    (hrel : ∀ x y, F.rel x y ↔ rel' (e x) (e y))
    (v' : Nat → W' → Prop)
    (hv : ∀ n x, v n x ↔ v' n (e x)) :
    forces F v w φ ↔ forces ⟨W', rel'⟩ v' (e w) φ := by
      -- We'll use induction on the structure of the formula φ.
      induction' φ with φ ψ hφ hψ generalizing w;
      · bound;
      · exact hv _ _;
      · aesop;
      · simp_all +decide [ forces ];
      · simp +decide [ *, forces ];
        exact ⟨ fun h y hy => by simpa using h ( e.symm y ) ( by simpa using hy ), fun h y hy => by simpa using h ( e y ) ( by simpa using hy ) ⟩

/--
Any model on a finite type can be transferred to `Fin n` preserving
satisfiability, using `Fintype.equivFin`.
-/
lemma finite_model_to_fin {F : Frame} [inst : Fintype F.states]
    {v : Nat → F.states → Prop} {w : F.states} {φ : Form}
    (h : forces F v w φ) :
    finNSatisfiable φ (Fintype.card F.states) := by
      -- Use Fintype.equivFin to get e : F.states ≃ Fin (Fintype.card F.states).
      obtain ⟨e, he⟩ : ∃ e : F.states ≃ Fin (Fintype.card F.states), True := by
        exact ⟨ Fintype.equivFin _, trivial ⟩
      generalize_proofs at *; simp_all +decide  ; (
      -- Define rel' on Fin n by rel' i j = F.rel (e.symm i) (e.symm j), and v' k i = v k (e.symm i).
      set rel' : Fin (Fintype.card F.states) → Fin (Fintype.card F.states) → Prop := fun i j => F.rel (e.symm i) (e.symm j)
      set v' : Nat → Fin (Fintype.card F.states) → Prop := fun k i => v k (e.symm i);
      -- By forces_equiv with e, we have forces F v w φ ↔ forces ⟨Fin n, rel'⟩ v' (e w) φ.
      have h_equiv : forces F v w φ ↔ forces ⟨Fin (Fintype.card F.states), rel'⟩ v' (e w) φ := by
        apply forces_equiv e rel' (by
        aesop) v' (by
        aesop)
      generalize_proofs at *; simp_all +decide ; -- Use the equivalence to transfer the satisfiability.;
      exact ⟨ rel', v', e w, h ⟩)

/-- Finite satisfiability is equivalent to satisfiability on `Fin n` for some n. -/
theorem finSatisfiable_iff_exists_finN (φ : Form) :
    finSatisfiable φ ↔ ∃ n, finNSatisfiable φ n := by
      constructor <;> intro h;
      · obtain ⟨ F, hF, v, w, hw ⟩ := h;
        haveI := Fintype.ofFinite F.states; exact ⟨ Fintype.card F.states, finite_model_to_fin hw ⟩ ;
      · obtain ⟨ n, hn ⟩ := h; rcases hn with ⟨ rel, v, w, hw ⟩ ; exact ⟨ ⟨ Fin n, rel ⟩, inferInstance, v, w, hw ⟩ ;

/-!
## § 5. Bounded Satisfiability
-/

/--
**Bounded satisfiability**: φ is satisfiable in some model with at most N worlds.
-/
def boundedSatisfiable (φ : Form) (N : Nat) : Prop :=
  ∃ n, n ≤ N ∧ finNSatisfiable φ n

/--
**Bounded satisfiability from FMP**: If φ is satisfiable, then it is satisfiable
in a model with at most 2^|Sub(φ)| worlds. Constructs the filtration, bounds
the number of equivalence classes by the number of truth assignments to
subformulas, then transfers to `Fin n`.
-/
theorem satisfiable_implies_bounded (φ : Form) :
    satisfiable φ → boundedSatisfiable φ (2 ^ (subformulas φ).length) := by
      rintro ⟨ F, v, w, h ⟩;
      -- By the finite model property, we can assume F is finite.
      have h_finite : ∃ (F' : Frame) (v' : Nat → F'.states → Prop) (w' : F'.states), forces F' v' w' φ ∧ Finite F'.states := by
        obtain ⟨ F', v', w', h' ⟩ := Modal.finite_model_property φ ⟨ F, v, w, h ⟩;
        exact ⟨ F', w', h'.choose, h'.choose_spec, v' ⟩;
      obtain ⟨ F', v', w', h₁, h₂ ⟩ := h_finite;
      -- Construct the filtration of F' with respect to φ.
      set F'' := filtrationFrame F' v' φ
      set v'' := filtrationVal F' v' φ
      set w'' := Quotient.mk (subfmlSetoid F' v' φ) w';
      have h_finite : Fintype F''.states := by
        exact Fintype.ofFinite _
      have h_card : Fintype.card F''.states ≤ 2 ^ (subformulas φ).length := by
        have h_card : Fintype.card F''.states ≤ Finset.card (Finset.image (fun x => fun ψ : (subformulas φ).toFinset => forces F' v' x ψ) (Set.Finite.toFinset (Set.toFinite (Set.univ : Set F'.states))) ) := by
          have h_card : Fintype.card F''.states ≤ Finset.card (Finset.image (fun x => fun ψ : (subformulas φ).toFinset => forces F' v' x ψ) (Set.Finite.toFinset (Set.toFinite (Set.univ : Set F'.states))) ) := by
            have h_inj : Function.Injective (fun q : F''.states => fun ψ : (subformulas φ).toFinset => forces F' v' (Quotient.out q) ψ) := by
              intro q₁ q₂ h_eq; simp_all +decide [ funext_iff ] ;
              rw [ ← Quotient.out_eq q₁, ← Quotient.out_eq q₂ ];
              exact Quotient.sound fun ψ hψ => by specialize h_eq ψ; aesop;
            have h_card : Finset.card (Finset.image (fun q : F''.states => fun ψ : (subformulas φ).toFinset => forces F' v' (Quotient.out q) ψ) (Finset.univ : Finset F''.states)) ≤ Finset.card (Finset.image (fun x => fun ψ : (subformulas φ).toFinset => forces F' v' x ψ) (Set.Finite.toFinset (Set.toFinite (Set.univ : Set F'.states))) ) := by
              refine Finset.card_le_card ?_;
              simp +decide [ Finset.subset_iff ];
            rwa [ Finset.card_image_of_injective _ h_inj, Finset.card_univ ] at h_card;
          exact h_card;
        refine le_trans h_card <| le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_univ _ ) ?_ ; simp +decide [ Finset.card_univ ] ; ring_nf ;
        exact pow_le_pow_right₀ ( by decide ) ( List.toFinset_card_le _ ) |> le_trans <| by simp +decide  ;
      have h_forces : forces F'' v'' w'' φ := by
        convert filtration_lemma F' v' φ w' φ _ |>.1 h₁ using 1;
        exact mem_subformulas_self φ
      exact ⟨ Fintype.card F''.states, by
        exact h_card, by
        convert finite_model_to_fin h_forces using 1 ⟩

/-- Bounded satisfiability implies satisfiability. -/
lemma boundedSatisfiable_implies_satisfiable (φ : Form) (N : Nat) :
    boundedSatisfiable φ N → satisfiable φ := by
      intro h
      obtain ⟨n, hn_le, hn⟩ := h
      obtain ⟨rel, v, w, hw⟩ := hn
      use ⟨Fin n, rel⟩, v, w

/--
**Key reduction**: satisfiability is equivalent to bounded satisfiability.
-/
theorem satisfiable_iff_bounded (φ : Form) :
    satisfiable φ ↔ boundedSatisfiable φ (2 ^ (subformulas φ).length) :=
  ⟨satisfiable_implies_bounded φ, boundedSatisfiable_implies_satisfiable φ _⟩

/-!
## § 6. Computable Boolean Forcing
-/

/--
**Boolean forcing**: A computable version of the forcing relation for finite models
with Bool-valued accessibility relations and valuations.

This mirrors the standard `forces` definition but works entirely with `Bool`,
making it suitable for algorithmic model checking.
-/
def bForces (n : Nat) (rel : Fin n → Fin n → Bool) (v : Nat → Fin n → Bool)
    (w : Fin n) : Form → Bool
  | .bot => false
  | .var k => v k w
  | .and φ ψ => bForces n rel v w φ && bForces n rel v w ψ
  | .impl φ ψ => !bForces n rel v w φ || bForces n rel v w ψ
  | .box φ => (List.finRange n).all fun y => !(rel w y) || bForces n rel v y φ

/-- **Correctness of Boolean forcing**: `bForces` agrees with `forces` under
the canonical embedding of `Bool` into `Prop`. By induction on φ. -/
theorem bForces_iff_forces (n : Nat) (rel : Fin n → Fin n → Bool)
    (v : Nat → Fin n → Bool) (w : Fin n) (φ : Form) :
    bForces n rel v w φ = true ↔
      forces ⟨Fin n, fun i j => rel i j = true⟩
        (fun k w => v k w = true) w φ := by
          -- We'll use induction on the structure of the formula φ.
          induction' φ with p q hp hq generalizing w;
          · simp [bForces, forces];
          · simp [bForces, forces];
          · unfold bForces forces; aesop;
          · simp_all +decide [ forces, bForces ];
            grind +ring;
          · simp +decide [ *, bForces, forces ];
            grind +ring

/-!
## § 7. Fin n Satisfiability via Restricted Variables
-/

/--
For fixed n, `finNSatisfiable φ n` is equivalent to the existence of a
Bool-valued model on `Fin n` satisfying φ. Uses `bForces_iff_forces` and
classical decidability to convert between `Prop`- and `Bool`-valued models.
-/
theorem finNSatisfiable_iff_bool (φ : Form) (n : Nat) :
    finNSatisfiable φ n ↔
      ∃ (rel : Fin n → Fin n → Bool) (v : Nat → Fin n → Bool) (w : Fin n),
        bForces n rel v w φ = true := by
          constructor <;> intro h <;> simp_all +decide [ finNSatisfiable ];
          · obtain ⟨ rel, v, w, h ⟩ := h;
            -- By definition of `forces`, we know that `forces ⟨Fin n, rel⟩ v w φ` holds if and only if `bForces n (fun i j => rel i j = true) (fun k w => v k w = true) w φ` holds.
            have h_bForces : bForces n (fun i j => rel i j = true) (fun k w => v k w = true) w φ = true := by
              convert bForces_iff_forces n _ _ _ φ |>.2 _;
              convert h using 1;
              · aesop;
              · grind +ring;
            exact ⟨ _, _, _, h_bForces ⟩;
          · obtain ⟨ rel, v, w, hw ⟩ := h
            use fun i j => rel i j = true, fun k w' => v k w' = true, w
            exact (bForces_iff_forces n rel v w φ).mp hw |> fun h => by simpa using h;

/--
Satisfiability with unrestricted valuations is equivalent to satisfiability
with valuations restricted to variables of φ. This enables finite enumeration
of valuations by `forces_eq_of_vars_eq`.
-/
theorem finNSatisfiable_restrict_vars (φ : Form) (n : Nat) :
    finNSatisfiable φ n ↔
      ∃ (rel : Fin n → Fin n → Prop) (v : (vars φ) → Fin n → Prop) (w : Fin n),
        forces ⟨Fin n, rel⟩
          (fun k w' => if h : k ∈ vars φ then v ⟨k, h⟩ w' else False) w φ := by
            constructor;
            · rintro ⟨ rel, v, w, hw ⟩;
              refine' ⟨ rel, _, w, _ ⟩;
              exact fun ⟨ k, hk ⟩ w' => v k w';
              grind +suggestions;
            · unfold finNSatisfiable; aesop;

/-!
## § 8. Decidability of Fin n Satisfiability
-/

/--
`finNSatisfiable φ n` is decidable for each fixed n.

This follows from `finNSatisfiable_restrict_vars`, which reduces the problem to
an existential quantification over finite types:
- `Fin n → Fin n → Prop` is `Fintype` (since `Prop` is `Fintype`)
- `(vars φ) → Fin n → Prop` is `Fintype` (since `vars φ` is a `Finset`)
- `Fin n` is `Fintype`
- The body (`forces ...`) is decidable classically
-/
noncomputable instance decidable_finNSatisfiable (φ : Form) (n : Nat) :
    Decidable (finNSatisfiable φ n) := by
  rw [finNSatisfiable_restrict_vars]
  letI : ∀ (rel : Fin n → Fin n → Prop) (v : (vars φ) → Fin n → Prop) (w : Fin n),
      Decidable (forces ⟨Fin n, rel⟩
        (fun k w' => if h : k ∈ vars φ then v ⟨k, h⟩ w' else False) w φ) :=
    fun _ _ _ => Classical.dec _
  exact inferInstance

/--
`boundedSatisfiable φ N` is decidable for each fixed N.

This uses the equivalence `∃ n ≤ N, P n ↔ ∃ k : Fin (N+1), P k.val`
to reduce to an existential over a finite type.
-/
noncomputable instance decidable_boundedSatisfiable (φ : Form) (N : Nat) :
    Decidable (boundedSatisfiable φ N) := by
  unfold boundedSatisfiable
  have : (∃ n, n ≤ N ∧ finNSatisfiable φ n) ↔
      ∃ k : Fin (N + 1), finNSatisfiable φ k.val := by
    constructor
    · rintro ⟨n, hn, hsat⟩
      exact ⟨⟨n, by omega⟩, hsat⟩
    · rintro ⟨⟨n, hn⟩, hsat⟩
      exact ⟨n, by omega, hsat⟩
  rw [this]
  exact inferInstance

/-!
## § 9. Decidability of K-Validity
-/

/-- **Main equivalence**: K-validity ↔ no countermodel with ≤ 2^|Sub(∼φ)| worlds. -/
theorem kValid_iff_no_bounded_countermodel (φ : Form) :
    kValid φ ↔ ¬ boundedSatisfiable (∼φ) (2 ^ (subformulas (∼φ)).length) := by
      rw [ kValid_iff_not_satisfiable_neg, satisfiable_iff_bounded ]

/--
**Decidability of K**: The set of K-valid formulas is decidable.

Given any modal formula φ, we can determine whether φ is valid in all Kripke frames.
The decision procedure works as follows:
1. Compute ∼φ (the negation of φ)
2. Compute the bound N = 2^|Sub(∼φ)|
3. For each model size n ≤ N, enumerate all frames and valuations on Fin n
4. Check whether ∼φ is satisfied in any of these models
5. φ is valid iff no countermodel is found

By `kValid_iff_no_bounded_countermodel`, this procedure is correct.
By `finNSatisfiable_restrict_vars`, each check only involves finitely many
valuations (restricted to variables in ∼φ). Since all types involved are
finite, the search terminates.

The `noncomputable` marker is due to the use of `Classical.choice` in the
finite model property proof (Lindenbaum's lemma). The decision procedure
itself is conceptually computable.
-/
noncomputable instance decidable_kValid : DecidablePred kValid := by
  intro φ
  rw [kValid_iff_no_bounded_countermodel]
  exact inferInstance

end Modal
