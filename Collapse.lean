/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# Syntactic Collapse Proofs via Semantic Bridge

This file formalizes the key axiom collapses that reduce 32 possible combinations
of {T, B, 4, D, 5} down to 16 distinct modal logics.

## Strategy: Semantic Bridge

Rather than constructing difficult Hilbert-style derivations directly, we use the
soundness–completeness bridge:

1. Show the target axiom is **semantically valid** in the frame class of the source logic.
2. Apply the **completeness theorem** to obtain a syntactic derivation.

This approach leverages the existing completeness results and avoids complex
syntactic manipulations in the Hilbert proof system.

For the harder collapses (D + B + 4 ⊢ T and D + B + 5 ⊢ T), where no single
completeness theorem matches the axiom set, we use direct Hilbert-system derivations
with the available proof infrastructure.

## Main Results

- `T5_proves_B`: T + 5 ⊢ B (reflexive + Euclidean frames validate symmetry)
- `T5_proves_4`: T + 5 ⊢ 4 (reflexive + Euclidean frames validate transitivity)
- `B5_proves_4`: B + 5 ⊢ 4 (symmetric + Euclidean frames validate transitivity)
- `DB4_proves_T`: D + B + 4 ⊢ T (serial + symmetric + transitive frames validate reflexivity)
- `DB5_proves_T`: D + B + 5 ⊢ T (derived from B+5⊢4 and D+B+4⊢T)

## References

- Blackburn, de Rijke, Venema. *Modal Logic*. Cambridge University Press, 2001.
  Chapter 4 on correspondences and frame class inclusions.
-/

import ModalLogic.Metatheory.Overview
import ModalLogic.Semantics.Overview

namespace Modal
open Modal BasicModal BasicModal.Modal BasicModal.ProofK

/-!
## § 1. T + 5 Collapses

Reflexive + Euclidean frames are equivalence relations, so S5 = T + 5.
The B and 4 axioms are redundant in the presence of T and 5.
-/

/--
**T + 5 ⊢ B**: The B axiom `φ → □◇φ` is derivable from T + 5 axioms.

**Semantic argument**: In equivalence frames (reflexive + Euclidean = S5 frames),
if φ holds at world w, then for any w' with R(w,w'), symmetry gives R(w',w),
so ◇φ holds at w' (witnessed by w). Hence □◇φ holds at w.
-/
theorem T5_proves_B : ∀ φ, S5Axioms ⊢K (φ ⊃ □(◇ φ)) := by
  intro φ
  apply completeness_S5
  intro F v hRefl hSymm _hTrans w
  simp [forces, dia, neg]
  intro hφ w' hRww'
  exact ⟨w, hSymm _ _ hRww', hφ⟩

/--
**T + 5 ⊢ 4**: The 4 axiom `□φ → □□φ` is derivable from T + 5 axioms.

**Semantic argument**: In equivalence frames, if □φ holds at w,
then for any w' with R(w,w') and w'' with R(w',w''), transitivity gives
R(w,w''), so φ holds at w''. Hence □□φ holds at w.
-/
theorem T5_proves_4 : ∀ φ, S5Axioms ⊢K (□ φ ⊃ □(□ φ)) := by
  intro φ
  apply completeness_S5
  intro F v _hRefl _hSymm hTrans w hBox w' hRww' w'' hRw'w''
  exact hBox w'' (hTrans _ _ _ hRww' hRw'w'')

/-!
## § 2. B + 5 Collapse

Symmetric + Euclidean implies transitive, so the 4 axiom is redundant
in KB5, giving KB5 = KB45.
-/

/--
**B + 5 ⊢ 4**: The 4 axiom `□φ → □□φ` is derivable from B + 5 axioms.

**Semantic argument**: In symmetric + Euclidean frames, given R(w,w') and R(w',w''):
symmetry on R(w,w') gives R(w',w), then Euclidean on R(w',w) and R(w',w'')
gives R(w,w''). So if □φ holds at w, φ holds at w'', giving □□φ.
-/
theorem B5_proves_4 : ∀ φ, KB5Axioms ⊢K (□ φ ⊃ □(□ φ)) := by
  intro φ
  apply completeness_KB5
  intro F v hSymm hEuclid w hBox w' hRww' w'' hRw'w''
  exact hBox w'' (hEuclid w' w w'' (hSymm w w' hRww') hRw'w'')

/-!
## § 3. D + B + 4 Collapse

Serial + symmetric + transitive implies reflexive, so the T axiom is
derivable from D + B + 4, giving KDB4 = S5.

Since no single completeness theorem matches KDBAxioms ∪ K4Axioms directly,
we construct a direct Hilbert-system derivation.
-/

/--
**D + B + 4 ⊢ T**: The T axiom `□φ → φ` is derivable from D + B + 4 axioms.

**Proof**: We prove the contrapositive ∼φ → ∼□φ using the Hilbert system:
1. B axiom: ∼φ → □◇∼φ
2. ◇∼φ ≡ ∼□φ (by double negation elimination inside box), so ∼φ → □∼□φ
3. D axiom: □∼□φ → ◇∼□φ
4. ◇∼□φ ≡ ∼□□φ (diamond-negation conversion)
5. 4 axiom contrapositive: ∼□□φ → ∼□φ
6. Chain: ∼φ → ∼□φ, then contrapositive gives □φ → φ
-/
theorem DB4_proves_T : ∀ φ, (KDBAxioms ∪ K4Axioms) ⊢K (□ φ ⊃ φ) := by
  intro φ
  -- Step 1: B axiom gives ∼φ → □◇∼φ
  have hB : KDBAxioms ⊢K (∼φ ⊃ □ (◇ ∼φ)) :=
    hyp (Or.inr ⟨_, rfl⟩)
  -- Step 2: ◇∼φ ≡ ∼□φ, convert to ∼φ → □∼□φ
  have hConv : KDBAxioms ⊢K (∼φ ⊃ □ (∼(□ φ))) := by
    have h1 : KDBAxioms ⊢K (◇ ∼φ ⊃ ∼(□ φ)) := dia_neg_to_not_box
    have h2 : KDBAxioms ⊢K (□ (◇ ∼φ) ⊃ □ (∼(□ φ))) := box_mono h1
    exact impl_chain2 hB h2
  -- Step 3: D axiom gives □∼□φ → ◇∼□φ
  have hD : KDBAxioms ⊢K (□ (∼(□ φ)) ⊃ ◇ (∼(□ φ))) :=
    hyp (Set.mem_union_left _ (Set.mem_setOf.mpr ⟨_, rfl⟩))
  -- Step 4: ◇∼□φ ≡ ∼□□φ
  have hConv2 : KDBAxioms ⊢K (◇ (∼(□ φ)) ⊃ ∼(□ (□ φ))) :=
    dia_neg_to_not_box
  -- Step 5: 4 axiom contrapositive: ∼□□φ → ∼□φ
  have h4 : K4Axioms ⊢K (□ φ ⊃ □ (□ φ)) := hyp ⟨φ, rfl⟩
  have h4contra : (KDBAxioms ∪ K4Axioms) ⊢K (∼(□ (□ φ)) ⊃ ∼(□ φ)) :=
    contrapos.mpr (weakening Set.subset_union_right h4)
  -- Step 6: Chain ∼φ → ∼□φ
  have hChain : (KDBAxioms ∪ K4Axioms) ⊢K (∼φ ⊃ ∼(□ φ)) := by
    apply cut (ψ := □ (∼(□ φ)))
    · exact weakening Set.subset_union_left hConv
    · apply cut (ψ := ◇ (∼(□ φ)))
      · exact weakening Set.subset_union_left hD
      · exact cut (weakening Set.subset_union_left hConv2) h4contra
  -- Step 7: Contrapositive gives □φ → φ
  exact mp contrapos_mpr hChain

/-!
## § 4. D + B + 5 Collapse

Serial + symmetric + Euclidean implies equivalence (since symmetric + Euclidean
implies transitive, then serial + symmetric + transitive implies reflexive),
so the T axiom is derivable from D + B + 5, giving KDB5 = S5.
-/

/-
If every axiom of AX₁ is provable from AX₂, then any derivation from AX₁
can be replayed in AX₂. This generalizes weakening from set inclusion to
provable inclusion.
-/
theorem proof_lift {AX₁ AX₂ : Ctx} {φ : Form}
    (haxioms : ∀ ψ ∈ AX₁, AX₂ ⊢K ψ)
    (hprf : AX₁ ⊢K φ) : AX₂ ⊢K φ := by
  induction hprf;
  all_goals try { solve_by_elim [ ProofK.mp ] };
  all_goals solve_by_elim [ ProofK.pl1, ProofK.pl2, ProofK.pl3, ProofK.pl4, ProofK.pl5, ProofK.pl6, ProofK.kdist, ProofK.nec ]

/-
**D + B + 5 ⊢ T**: The T axiom `□φ → φ` is derivable from D + B + 5 axioms.

**Proof**: We show that every axiom of KDBAxioms ∪ K4Axioms is provable from
KDBAxioms ∪ K5Axioms (using B5_proves_4 for the 4 axioms), and then lift
the proof of DB4_proves_T via proof_lift.
-/
theorem DB5_proves_T : ∀ φ, (KDBAxioms ∪ K5Axioms) ⊢K (□ φ ⊃ φ) := by
  intro φ
  apply proof_lift;
  case AX₁ => exact KDBAxioms ∪ K4Axioms;
  · intro ψ hψ;
    cases hψ <;> simp_all +decide [ KDBAxioms, K4Axioms ];
    obtain ⟨ ψ, rfl ⟩ := ‹∃ ψ_1, ψ = □ ψ_1 ⟹ □ □ ψ_1›;
    apply B5_proves_4 ψ |> fun h => proof_lift (by
    intro ψ hψ; cases hψ <;> simp_all +decide [ KB5Axioms, KDAxioms, KBAxioms, K5Axioms ] ;) h;
  · exact DB4_proves_T φ

end Modal
