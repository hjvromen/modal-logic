/-
Copyright (c) 2026 Huub Vromen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huub Vromen

# The Modal Logic Cube — Full Enumeration of 16 Normal Modal Logics

This file presents a comprehensive enumeration and organization of **all 16 distinct
normal modal logics** that can be formed by combining the five fundamental axiom
schemas T, B, 4, D, and 5.

## Core Axiom Schemas

- **T**: □φ → φ (reflexivity)
- **B**: φ → □◇φ (symmetry)
- **4**: □φ → □□φ (transitivity)
- **D**: □φ → ◇φ (seriality)
- **5**: ◇φ → □◇φ (Euclidean property)

## The Classical Cube (T, B, 4)

The traditional "modal logic cube" is built from T, B, and 4:

```
          KTB4 = S5
         /    |    \
       KT4   KTB   KB4
      = S4    |      |
        \    KT    KB
         \  = T   /
          \  |  /
            K
          (base)
```

Each vertex is a logic; edges go upward to indicate extension (adding axioms).
All 8 logics have proven **soundness** and **completeness** with respect to
their corresponding frame classes. In fact, all **16 distinct** logics now have
proven soundness and completeness.

## Beyond the Cube: The Full Picture with D and 5

With 5 axiom schemas {T, B, 4, D, 5}, there are 2^5 = 32 possible subsets.
However, many collapse to the same logic due to key interdependencies:

### Collapse Rules

1. **T implies D**: Reflexive frames are serial, so adding D to any logic
   containing T is redundant. Thus KTD = KT, KTBD = KTB, KT4D = S4, etc.

2. **T + 5 = equivalence**: Reflexive + Euclidean frames are equivalence
   relations, giving both symmetry and transitivity. So KT5 = S5.

3. **Symmetric + Euclidean → Transitive**: From R(x,y), symmetry gives R(y,x);
   then R(y,x) ∧ R(y,z) with Euclidean gives R(x,z). So KB5 = KB45.

4. **Serial + Symmetric + Transitive → Reflexive**: From seriality, ∃y. R(x,y);
   symmetry gives R(y,x); then R(x,y) ∧ R(y,x) with transitivity gives R(x,x).
   So KDB4 = KTB4 = S5.

5. **Serial + Symmetric + Euclidean → Equivalence**: Symmetric + Euclidean →
   Transitive (rule 3), then Serial + Symmetric + Transitive → Reflexive (rule 4).
   So KDB5 = S5.

### The 16 Distinct Logics

After applying all collapse rules, exactly **16 distinct logics** remain:

```
                       S5 = KTB4 = KT5 = KDB4 = KDB5
                      / |  \      |        \
                   S4  KTB  KB4  KD45      KB5
                   |    |    |   / |        |
                  KT   KB   K4  KD5   K45  KD4   KDB
                   \    |   / | /  \   |  / |    /
                    \   |  /  K5    KD  | /  |  /
                     \  | /   |       \ |/   | /
                       K -----+--------+-----+
                     (base)
```

## Soundness and Completeness Summary

| Logic    | Axioms  | Frame Class                     | Soundness | Completeness |
|----------|---------|---------------------------------|-----------|--------------|
| K        | ∅       | All frames                      | ✓         | ✓            |
| KT       | T       | Reflexive                       | ✓         | ✓            |
| KB       | B       | Symmetric                       | ✓         | ✓            |
| K4       | 4       | Transitive                      | ✓         | ✓            |
| K5       | 5       | Euclidean                       | ✓         | ✓            |
| KD       | D       | Serial                          | ✓         | ✓            |
| KTB      | T+B     | Refl+Symm                       | ✓         | ✓            |
| KT4=S4   | T+4     | Refl+Trans                      | ✓         | ✓            |
| KB4      | B+4     | Symm+Trans                      | ✓         | ✓            |
| KDB      | D+B     | Serial+Symm                     | ✓         | ✓            |
| KD4      | D+4     | Serial+Trans                    | ✓         | ✓            |
| KD5      | D+5     | Serial+Euclid                   | ✓         | ✓            |
| K45      | 4+5     | Trans+Euclid                    | ✓         | ✓            |
| KB5=KB45 | B+5     | Symm+Euclid (+Trans)            | ✓         | ✓            |
| KD45     | D+4+5   | Serial+Trans+Euclid             | ✓         | ✓            |
| KTB4=S5  | T+B+4   | Equivalence                     | ✓         | ✓            |

## The Equivalence Characterization

A key structural theorem underpins the relationship between the cube and the 5 axiom:

> **Theorem**: A frame has an equivalence relation if and only if it is
> both reflexive and Euclidean.

This explains why S5 can be axiomatized as either T + B + 4 or simply T + 5.
The Euclidean property, when combined with reflexivity, automatically gives
both symmetry and transitivity.

## Frame Class Inclusions

```
              equivClass
           /    |     |    \
  refTransClass  refSymmClass  symmTransClass  refEuclidClass
        \        |        /          |
   refClass  symmClass  transClass  euclidClass  serialClass
```

Key inclusions:
- equivClass = refClass ∩ euclidClass
- refClass ⊆ serialClass
- equivClass ⊆ refTransClass ∩ refSymmClass ∩ symmTransClass
- symmEuclidClass ⊆ symmTransClass (symm + Euclidean → trans)
- serialSymmClass ∩ transClass ⊆ equivClass (serial + symm + trans → refl)
-/

import ModalLogic.Metatheory.Overview
import ModalLogic.Semantics.Overview

namespace Modal
open Modal BasicModal

/-!
## § 1. Frame Class Inclusion Theorems

These theorems establish the lattice structure of frame classes in the cube.
-/

/-- Equivalence frames are reflexive-symmetric. -/
theorem equivClass_sub_refSymmClass : equivClass ⊆ refSymmClass := by
  intro F hF
  exact ⟨hF.refl, @Equivalence.symm _ _ hF⟩

/-- Equivalence frames are symmetric-transitive. -/
theorem equivClass_sub_symmTransClass : equivClass ⊆ symmTransClass := by
  intro F hF
  exact ⟨@Equivalence.symm _ _ hF, fun _ _ _ => hF.trans⟩

/-- Equivalence frames are reflexive-transitive (= S4 frames). -/
theorem equivClass_sub_refTransClass : equivClass ⊆ refTransClass := by
  intro F hF
  exact ⟨hF.refl, fun _ _ _ => hF.trans⟩

/-- Reflexive-symmetric frames are reflexive. -/
theorem refSymmClass_sub_refClass : refSymmClass ⊆ refClass := by
  intro F hF
  exact hF.1

/-- Reflexive-symmetric frames are symmetric. -/
theorem refSymmClass_sub_symmClass : refSymmClass ⊆ symmClass := by
  intro F hF
  exact hF.2

/-- Reflexive-transitive frames are reflexive. -/
theorem refTransClass_sub_refClass : refTransClass ⊆ refClass := by
  intro F hF
  exact hF.1

/-- Reflexive-transitive frames are transitive. -/
theorem refTransClass_sub_transClass : refTransClass ⊆ transClass := by
  intro F hF
  exact hF.2

/-- Symmetric-transitive frames are symmetric. -/
theorem symmTransClass_sub_symmClass : symmTransClass ⊆ symmClass := by
  intro F hF
  exact hF.1

/-- Symmetric-transitive frames are transitive. -/
theorem symmTransClass_sub_transClass : symmTransClass ⊆ transClass := by
  intro F hF
  exact hF.2

/-!
## § 2. Frame Class Inclusions Involving D and 5

These theorems establish how serial and Euclidean frame classes relate
to the rest of the hierarchy.
-/

/-- Reflexive frames are serial: every reflexive frame is serial. -/
theorem refClass_sub_serialClass : refClass ⊆ serialClass := by
  intro F hRefl x
  exact ⟨x, hRefl x⟩

/-- Equivalence frames are Euclidean. -/
theorem equivClass_sub_euclidClass : equivClass ⊆ euclidClass := by
  intro F hEquiv x y z hxy hxz
  exact hEquiv.trans (hEquiv.symm hxy) hxz

/-- Equivalence frames are serial (corollary of reflexivity). -/
theorem equivClass_sub_serialClass : equivClass ⊆ serialClass := by
  intro F hEquiv
  exact refClass_sub_serialClass (equivClass_sub_refTransClass hEquiv).1

/-- Reflexive Euclidean frames are equivalence frames. -/
theorem refEuclid_sub_equivClass :
    (refClass ∩ euclidClass : Set Frame.{0}) ⊆ equivClass := by
  intro F ⟨hRefl, hEuclid⟩
  exact (equivRefEuclid F).mpr ⟨hRefl, hEuclid⟩

/-- Equivalence frames are exactly reflexive Euclidean frames (the key characterization). -/
theorem equivClass_eq_refEuclid :
    equivClass = (refClass ∩ euclidClass : Set Frame.{0}) := by
  ext F
  exact equivRefEuclid F

/-!
### Frame class inclusions for the 4 new logics
-/

/-- Serial-symmetric frames are serial. -/
theorem serialSymmClass_sub_serialClass : serialSymmClass ⊆ serialClass := by
  intro F hF; exact hF.1

/-- Serial-symmetric frames are symmetric. -/
theorem serialSymmClass_sub_symmClass : serialSymmClass ⊆ symmClass := by
  intro F hF; exact hF.2

/-- Serial-transitive frames are serial. -/
theorem serialTransClass_sub_serialClass : serialTransClass ⊆ serialClass := by
  intro F hF; exact hF.1

/-- Serial-transitive frames are transitive. -/
theorem serialTransClass_sub_transClass : serialTransClass ⊆ transClass := by
  intro F hF; exact hF.2

/-- Transitive-Euclidean frames are transitive. -/
theorem transEuclidClass_sub_transClass : transEuclidClass ⊆ transClass := by
  intro F hF; exact hF.1

/-- Transitive-Euclidean frames are Euclidean. -/
theorem transEuclidClass_sub_euclidClass : transEuclidClass ⊆ euclidClass := by
  intro F hF; exact hF.2

/-- Symmetric-Euclidean frames are symmetric. -/
theorem symmEuclidClass_sub_symmClass : symmEuclidClass ⊆ symmClass := by
  intro F hF; exact hF.1

/-- Symmetric-Euclidean frames are Euclidean. -/
theorem symmEuclidClass_sub_euclidClass : symmEuclidClass ⊆ euclidClass := by
  intro F hF; exact hF.2

/-- **Key collapse**: Symmetric + Euclidean implies transitive.
    From R(x,y) and R(y,z): symmetry gives R(y,x), then Euclidean on
    R(y,x) and R(y,z) gives R(x,z). -/
theorem symmEuclidClass_sub_symmTransClass : symmEuclidClass ⊆ symmTransClass := by
  intro F ⟨hSymm, hEuclid⟩
  exact ⟨hSymm, fun {x y z} hxy hyz => hEuclid (hSymm hxy) hyz⟩

/-- Equivalence frames are symmetric-Euclidean. -/
theorem equivClass_sub_symmEuclidClass : equivClass ⊆ symmEuclidClass := by
  intro F hEquiv
  constructor
  · exact @Equivalence.symm _ _ hEquiv
  · intro x y z hxy hxz
    exact hEquiv.trans (hEquiv.symm hxy) hxz

/-- Equivalence frames are serial-symmetric. -/
theorem equivClass_sub_serialSymmClass : equivClass ⊆ serialSymmClass := by
  intro F hEquiv
  exact ⟨refClass_sub_serialClass hEquiv.refl, @Equivalence.symm _ _ hEquiv⟩

/-- Equivalence frames are serial-transitive. -/
theorem equivClass_sub_serialTransClass : equivClass ⊆ serialTransClass := by
  intro F hEquiv
  exact ⟨refClass_sub_serialClass hEquiv.refl, fun {_ _ _} => hEquiv.trans⟩

/-- Equivalence frames are transitive-Euclidean. -/
theorem equivClass_sub_transEuclidClass : equivClass ⊆ transEuclidClass := by
  intro F hEquiv
  constructor
  · intro x y z hxy hyz; exact hEquiv.trans hxy hyz
  · intro x y z hxy hxz
    exact hEquiv.trans (hEquiv.symm hxy) hxz

/-- **Key collapse**: Serial + symmetric + transitive → reflexive → equivalence. -/
theorem serialSymmTrans_sub_equivClass :
    (serialSymmClass ∩ transClass : Set Frame.{0}) ⊆ equivClass := by
  intro F ⟨⟨hSerial, hSymm⟩, hTrans⟩
  refine ⟨fun x => ?_, @hSymm, @hTrans⟩
  obtain ⟨y, hxy⟩ := hSerial x
  exact hTrans hxy (hSymm hxy)

/-!
## § 3. Axiom Set Inclusions

If logic L₁ extends logic L₂ (L₂'s axioms ⊆ L₁'s axioms), then everything
provable in L₂ is provable in L₁. We establish these inclusion relationships.
-/

/-- K's axioms (∅) are contained in every logic's axioms. -/
theorem K_sub_any (AX : Ctx) : (∅ : Ctx) ⊆ AX := Set.empty_subset AX

/-- T axioms are contained in S4 axioms. -/
theorem T_sub_S4 : TAxioms ⊆ S4Axioms := Set.subset_union_left

/-- T axioms are contained in KTB axioms. -/
theorem T_sub_KTB : TAxioms ⊆ KTBAxioms := Set.subset_union_left

/-- T axioms are contained in S5 axioms. -/
theorem T_sub_S5 : TAxioms ⊆ S5Axioms := Set.subset_union_left

/-- KB axioms are contained in KTB axioms. -/
theorem KB_sub_KTB : KBAxioms ⊆ KTBAxioms := Set.subset_union_right

/-- KB axioms are contained in KB4 axioms. -/
theorem KB_sub_KB4 : KBAxioms ⊆ KB4Axioms := Set.subset_union_left

/-- K4 axioms are contained in S4 axioms. -/
theorem K4_sub_S4 : K4Axioms ⊆ S4Axioms := Set.subset_union_right

/-- K4 axioms are contained in KB4 axioms. -/
theorem K4_sub_KB4 : K4Axioms ⊆ KB4Axioms := Set.subset_union_right

/-- S5 axioms = T axioms + K5 axioms (the 5 axiom is exactly the non-T part of S5). -/
theorem S5_eq_T_plus_K5 : S5Axioms = TAxioms ∪ K5Axioms := rfl

/-- K5 axioms are contained in S5 axioms. -/
theorem K5_sub_S5 : K5Axioms ⊆ S5Axioms := Set.subset_union_right

/-- KD axioms are contained in KD5 axioms. -/
theorem KD_sub_KD5 : KDAxioms ⊆ KD5Axioms := Set.subset_union_left

/-- K5 axioms are contained in KD5 axioms. -/
theorem K5_sub_KD5 : K5Axioms ⊆ KD5Axioms := Set.subset_union_right

/-- KD axioms are contained in KD45 axioms. -/
theorem KD_sub_KD45 : KDAxioms ⊆ KD45Axioms := by
  intro φ hφ
  left; left; exact hφ

/-- K4 axioms are contained in KD45 axioms. -/
theorem K4_sub_KD45 : K4Axioms ⊆ KD45Axioms := by
  intro φ hφ
  left; right; exact hφ

/-- K5 axioms are contained in KD45 axioms. -/
theorem K5_sub_KD45 : K5Axioms ⊆ KD45Axioms := by
  intro φ hφ
  right; exact hφ

/-- KD axioms are contained in KDB axioms. -/
theorem KD_sub_KDB : KDAxioms ⊆ KDBAxioms := Set.subset_union_left

/-- KB axioms are contained in KDB axioms. -/
theorem KB_sub_KDB : KBAxioms ⊆ KDBAxioms := Set.subset_union_right

/-- KD axioms are contained in KD4 axioms. -/
theorem KD_sub_KD4 : KDAxioms ⊆ KD4Axioms := Set.subset_union_left

/-- K4 axioms are contained in KD4 axioms. -/
theorem K4_sub_KD4 : K4Axioms ⊆ KD4Axioms := Set.subset_union_right

/-- K4 axioms are contained in K45 axioms. -/
theorem K4_sub_K45 : K4Axioms ⊆ K45Axioms := Set.subset_union_left

/-- K5 axioms are contained in K45 axioms. -/
theorem K5_sub_K45 : K5Axioms ⊆ K45Axioms := Set.subset_union_right

/-- KB axioms are contained in KB5 axioms. -/
theorem KB_sub_KB5 : KBAxioms ⊆ KB5Axioms := Set.subset_union_left

/-- K5 axioms are contained in KB5 axioms. -/
theorem K5_sub_KB5 : K5Axioms ⊆ KB5Axioms := Set.subset_union_right

/-!
## § 4. Provability Monotonicity

If AX₁ ⊆ AX₂, then Γ ⊢_{AX₁} φ implies Γ ⊢_{AX₂} φ.
-/

/-- Provability is monotone in the axiom set. -/
theorem ProofK_monotone {AX₁ AX₂ : Ctx} {φ : Form} (h : AX₁ ⊆ AX₂) :
    ProofK AX₁ φ → ProofK AX₂ φ := by
  intro hprf
  induction hprf with
  | hyp hmem => exact ProofK.hyp (h hmem)
  | pl1 => exact ProofK.pl1
  | pl2 => exact ProofK.pl2
  | pl3 => exact ProofK.pl3
  | pl4 => exact ProofK.pl4
  | pl5 => exact ProofK.pl5
  | pl6 => exact ProofK.pl6
  | kdist => exact ProofK.kdist
  | mp _ _ ih1 ih2 => exact ProofK.mp ih1 ih2
  | nec _ ih => exact ProofK.nec ih

/-- K theorems are provable in any extension. -/
theorem K_provable_in_any {AX : Ctx} {φ : Form} :
    ProofK ∅ φ → ProofK AX φ :=
  ProofK_monotone (K_sub_any AX)

/-!
## § 5. The Full Cube: Soundness and Completeness Summary

All 16 distinct logics have verified soundness and completeness.
We collect the statements here for reference.
-/

-- Base: K
#check @soundness         -- K soundness
#check @completeness_K    -- K completeness

-- Level 1: KT, KB, K4
#check @TSoundness        -- KT soundness
#check @completeness_T    -- KT completeness
#check @KBSoundness       -- KB soundness
#check @completeness_KB   -- KB completeness
#check @K4Soundness       -- K4 soundness
#check @completeness_K4   -- K4 completeness

-- Level 2: KTB, KT4=S4, KB4
#check @KTBSoundness      -- KTB soundness
#check @completeness_KTB  -- KTB completeness
#check @S4Soundness       -- S4 soundness
#check @completeness_S4   -- S4 completeness
#check @KB4Soundness      -- KB4 soundness
#check @completeness_KB4  -- KB4 completeness

-- Top: KTB4=S5
#check @S5Soundness       -- S5 soundness
#check @completeness_S5   -- S5 completeness

/-!
## § 6. D and 5 Axiom Logics: Soundness and Completeness

Logics involving the D (seriality) and 5 (Euclidean) axioms.
-/

-- KD: D axiom alone
#check @KDSoundness       -- KD soundness (serial frames)
#check @completeness_KD   -- KD completeness

-- K5: 5 axiom alone
#check @K5Soundness       -- K5 soundness (Euclidean frames)
#check @completeness_K5   -- K5 completeness

-- KD5: D + 5 axioms
#check @KD5Soundness      -- KD5 soundness (serial + Euclidean frames)
#check @completeness_KD5  -- KD5 completeness

-- KD45: D + 4 + 5 axioms
#check @KD45Soundness     -- KD45 soundness (serial + transitive + Euclidean frames)
#check @completeness_KD45 -- KD45 completeness

/-!
## § 6b. The 4 Additional Logics: Soundness and Completeness

The four logics that complete the enumeration to 16.
All have proven soundness and completeness.
-/

-- KDB: D + B axioms
#check @KDBSoundness      -- KDB soundness (serial + symmetric frames)
#check @completeness_KDB  -- KDB completeness

-- KD4: D + 4 axioms
#check @KD4Soundness      -- KD4 soundness (serial + transitive frames)
#check @completeness_KD4  -- KD4 completeness

-- K45: 4 + 5 axioms
#check @K45Soundness      -- K45 soundness (transitive + Euclidean frames)
#check @completeness_K45  -- K45 completeness

-- KB5: B + 5 axioms
#check @KB5Soundness      -- KB5 soundness (symmetric + Euclidean frames)
#check @completeness_KB5  -- KB5 completeness

/-!
## § 7. Validity Propagation Through the Cube

If φ is valid in frame class C₁ and C₂ ⊆ C₁, then φ is valid in C₂.
We use this to show that theorems propagate upward through the cube.
-/

/-- Validity in all frames implies validity in reflexive frames. -/
theorem K_valid_implies_T_valid {φ : Form} :
    (∀ (F : Frame.{0}) v x, forces F v x φ) → FValid φ refClass :=
  fun h F _ v x => h F v x

/-- Validity in all frames implies validity in symmetric frames. -/
theorem K_valid_implies_KB_valid {φ : Form} :
    (∀ (F : Frame.{0}) v x, forces F v x φ) → FValid φ symmClass :=
  fun h F _ v x => h F v x

/-- Validity in all frames implies validity in transitive frames. -/
theorem K_valid_implies_K4_valid {φ : Form} :
    (∀ (F : Frame.{0}) v x, forces F v x φ) → FValid φ transClass :=
  fun h F _ v x => h F v x

/-- Validity in all frames implies validity in Euclidean frames. -/
theorem K_valid_implies_K5_valid {φ : Form} :
    (∀ (F : Frame.{0}) v x, forces F v x φ) → FValid φ euclidClass :=
  fun h F _ v x => h F v x

/-- Validity in all frames implies validity in serial frames. -/
theorem K_valid_implies_KD_valid {φ : Form} :
    (∀ (F : Frame.{0}) v x, forces F v x φ) → FValid φ serialClass :=
  fun h F _ v x => h F v x

/-- Validity in reflexive frames implies validity in reflexive-symmetric frames. -/
theorem T_valid_implies_KTB_valid {φ : Form} :
    FValid φ refClass → FValid φ refSymmClass :=
  validMonotone refSymmClass_sub_refClass

/-- Validity in reflexive frames implies validity in reflexive-transitive frames. -/
theorem T_valid_implies_S4_valid {φ : Form} :
    FValid φ refClass → FValid φ refTransClass :=
  validMonotone refTransClass_sub_refClass

/-- Validity in symmetric frames implies validity in reflexive-symmetric frames. -/
theorem KB_valid_implies_KTB_valid {φ : Form} :
    FValid φ symmClass → FValid φ refSymmClass :=
  validMonotone refSymmClass_sub_symmClass

/-- Validity in symmetric frames implies validity in symmetric-transitive frames. -/
theorem KB_valid_implies_KB4_valid {φ : Form} :
    FValid φ symmClass → FValid φ symmTransClass :=
  validMonotone symmTransClass_sub_symmClass

/-- Validity in transitive frames implies validity in reflexive-transitive frames. -/
theorem K4_valid_implies_S4_valid {φ : Form} :
    FValid φ transClass → FValid φ refTransClass :=
  validMonotone refTransClass_sub_transClass

/-- Validity in transitive frames implies validity in symmetric-transitive frames. -/
theorem K4_valid_implies_KB4_valid {φ : Form} :
    FValid φ transClass → FValid φ symmTransClass :=
  validMonotone symmTransClass_sub_transClass

/-- Validity in reflexive-symmetric frames implies validity in equivalence frames. -/
theorem KTB_valid_implies_S5_valid {φ : Form} :
    FValid φ refSymmClass → FValid φ equivClass :=
  validMonotone equivClass_sub_refSymmClass

/-- Validity in reflexive-transitive frames implies validity in equivalence frames. -/
theorem S4_valid_implies_S5_valid {φ : Form} :
    FValid φ refTransClass → FValid φ equivClass :=
  validMonotone equivClass_sub_refTransClass

/-- Validity in symmetric-transitive frames implies validity in equivalence frames. -/
theorem KB4_valid_implies_S5_valid {φ : Form} :
    FValid φ symmTransClass → FValid φ equivClass :=
  validMonotone equivClass_sub_symmTransClass

/-!
### Validity propagation for D and 5
-/

/-- Validity in serial frames implies validity in reflexive frames
(since reflexive ⊆ serial, every formula valid over all serial frames
is a fortiori valid over reflexive frames). -/
theorem KD_valid_implies_T_valid {φ : Form} :
    FValid φ serialClass → FValid φ refClass :=
  validMonotone refClass_sub_serialClass

/-- Validity in Euclidean frames implies validity in equivalence frames
(since equivalence ⊆ Euclidean). -/
theorem K5_valid_implies_S5_valid {φ : Form} :
    FValid φ euclidClass → FValid φ equivClass :=
  validMonotone equivClass_sub_euclidClass

/-- Validity in serial frames implies validity in equivalence frames
(since equivalence frames are serial). -/
theorem KD_valid_implies_S5_valid {φ : Form} :
    FValid φ serialClass → FValid φ equivClass :=
  validMonotone equivClass_sub_serialClass

/-!
### Validity propagation for the 4 new logics
-/

/-- Validity in symmetric frames implies validity in symmetric-Euclidean frames. -/
theorem KB_valid_implies_KB5_valid {φ : Form} :
    FValid φ symmClass → FValid φ symmEuclidClass :=
  validMonotone symmEuclidClass_sub_symmClass

/-- Validity in Euclidean frames implies validity in symmetric-Euclidean frames. -/
theorem K5_valid_implies_KB5_valid {φ : Form} :
    FValid φ euclidClass → FValid φ symmEuclidClass :=
  validMonotone symmEuclidClass_sub_euclidClass

/-- Validity in serial frames implies validity in serial-symmetric frames. -/
theorem KD_valid_implies_KDB_valid {φ : Form} :
    FValid φ serialClass → FValid φ serialSymmClass :=
  validMonotone serialSymmClass_sub_serialClass

/-- Validity in symmetric frames implies validity in serial-symmetric frames. -/
theorem KB_valid_implies_KDB_valid {φ : Form} :
    FValid φ symmClass → FValid φ serialSymmClass :=
  validMonotone serialSymmClass_sub_symmClass

/-- Validity in serial frames implies validity in serial-transitive frames. -/
theorem KD_valid_implies_KD4_valid {φ : Form} :
    FValid φ serialClass → FValid φ serialTransClass :=
  validMonotone serialTransClass_sub_serialClass

/-- Validity in transitive frames implies validity in serial-transitive frames. -/
theorem K4_valid_implies_KD4_valid {φ : Form} :
    FValid φ transClass → FValid φ serialTransClass :=
  validMonotone serialTransClass_sub_transClass

/-- Validity in transitive frames implies validity in transitive-Euclidean frames. -/
theorem K4_valid_implies_K45_valid {φ : Form} :
    FValid φ transClass → FValid φ transEuclidClass :=
  validMonotone transEuclidClass_sub_transClass

/-- Validity in Euclidean frames implies validity in transitive-Euclidean frames. -/
theorem K5_valid_implies_K45_valid {φ : Form} :
    FValid φ euclidClass → FValid φ transEuclidClass :=
  validMonotone transEuclidClass_sub_euclidClass

/-- Validity in symmetric-Euclidean frames implies validity in equivalence frames. -/
theorem KB5_valid_implies_S5_valid {φ : Form} :
    FValid φ symmEuclidClass → FValid φ equivClass :=
  validMonotone equivClass_sub_symmEuclidClass

/-!
## § 8. Frame Class Characterizations

Key structural theorems connecting modal axioms to frame properties.
-/

/-- Equivalence frames are exactly the reflexive-symmetric-transitive frames. -/
theorem equivClass_eq_refSymmTrans :
    equivClass = refClass ∩ symmClass ∩ transClass := by
  ext F
  simp only [equivClass, refClass, symmClass, transClass,
             Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro hE
    exact ⟨⟨hE.refl, @Equivalence.symm _ _ hE⟩, @Equivalence.trans _ _ hE⟩
  · intro ⟨⟨hR, hS⟩, hT⟩
    exact ⟨hR, @hS, @hT⟩

/-- **The D-5 Characterization**: Equivalence frames = reflexive ∩ Euclidean.

This is a fundamental result explaining why S5 = T + 5 works.
The Euclidean property, combined with reflexivity, automatically yields
both symmetry and transitivity.

- **Symmetry from ref + Euclidean**: Given R(x,y), reflexivity gives R(x,x),
  and Euclidean on R(x,y) and R(x,x) gives R(y,x).

- **Transitivity from ref + Euclidean**: Given R(x,y) and R(y,z), the
  symmetry we just derived gives R(y,x). Then Euclidean on R(y,x) and
  R(y,z) gives R(x,z).
-/
theorem equivClass_eq_refEuclidClass :
    equivClass = (refClass ∩ euclidClass : Set Frame.{0}) := equivClass_eq_refEuclid

/-- **Symmetric + Euclidean = Symmetric + Transitive + Euclidean**.
    The Euclidean property with symmetry already implies transitivity,
    so adding transitivity explicitly is redundant. This explains why
    KB5 = KB45 as modal logics. -/
theorem symmEuclidClass_eq_symmTransEuclidClass :
    symmEuclidClass = (symmTransClass ∩ euclidClass : Set Frame.{0}) := by
  ext F
  simp only [symmEuclidClass, symmTransClass, euclidClass,
             Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro ⟨hSymm, hEuclid⟩
    exact ⟨⟨hSymm, fun {x y z} hxy hyz => hEuclid (hSymm hxy) hyz⟩, hEuclid⟩
  · intro ⟨⟨hSymm, _⟩, hEuclid⟩
    exact ⟨hSymm, hEuclid⟩

/-- **Serial + symmetric + transitive = equivalence**.
    Adding transitivity to serial-symmetric frames forces reflexivity,
    which together with symmetry and transitivity gives an equivalence relation.
    This explains why KDB4 collapses to S5. -/
theorem serialSymmTrans_eq_equivClass :
    (serialSymmClass ∩ transClass : Set Frame.{0}) = equivClass := by
  ext F
  constructor
  · intro ⟨⟨hSerial, hSymm⟩, hTrans⟩
    refine ⟨fun x => ?_, @hSymm, @hTrans⟩
    obtain ⟨y, hxy⟩ := hSerial x
    exact hTrans hxy (hSymm hxy)
  · intro hEquiv
    exact ⟨⟨refClass_sub_serialClass hEquiv.refl, @Equivalence.symm _ _ hEquiv⟩,
           fun {_ _ _} => hEquiv.trans⟩

/-!
## § 9. Correspondence Theory Summary

Each modal axiom corresponds to a frame property. These correspondences
are proven as frame definability theorems in `Definability.lean`.
-/

-- T axiom defines reflexivity
#check @BasicModal.refDef      -- □p → p ↔ reflexive

-- B axiom defines symmetry
#check @BasicModal.symmDef     -- p → □◇p ↔ symmetric

-- 4 axiom defines transitivity
#check @BasicModal.transDef    -- □p → □□p ↔ transitive

-- 5 axiom defines the Euclidean property
#check @BasicModal.euclidDef   -- ◇p → □◇p ↔ Euclidean

-- D axiom defines seriality
#check @BasicModal.serialDef   -- □p → ◇p ↔ serial

/-!
## § 10. The D Axiom: Seriality and Its Role

The D axiom (□φ → ◇φ) expresses that necessity implies possibility.
Semantically, it says every world has at least one accessible world (seriality).

### D vs T

The D axiom is strictly weaker than T:
- T says □φ → φ (what's necessary is true)
- D says □φ → ◇φ (what's necessary is at least possible)

Every reflexive frame is serial (a world always accesses itself), so
T implies D semantically. But serial frames need not be reflexive.

### Applications

KD is the base logic for **deontic reasoning** (the logic of obligation):
- □φ = "φ is obligatory"
- ◇φ = "φ is permitted"
- D axiom = "whatever is obligatory is permitted" (consistency of obligations)

The seriality condition ensures there is always an "ideal world" accessible
from every world, preventing the system from having inconsistent obligations.
-/

/--
**T axiom implies D axiom** (reflexivity implies seriality).

In the logic T, we can derive □φ → ◇φ for any formula φ.

**Proof**: From the T axiom we get □φ → φ. We also derive φ → ◇φ
by showing that if φ holds and □¬φ held, then by T we'd get ¬φ,
a contradiction. Chaining these two implications via cut gives □φ → ◇φ.
-/
theorem T_implies_D : ∀ φ : Form, ProofK TAxioms (□φ ⊃ ◇φ) := by
  intro φ
  -- Step 1: T axiom gives □φ → φ
  have hT : ProofK TAxioms (□φ ⊃ φ) := ProofK.hyp ⟨φ, rfl⟩
  -- Step 2: Derive φ → ◇φ (i.e., φ → ¬□¬φ) in T
  have hPhiDia : TAxioms ⊢K φ ⊃ ◇ φ := by
    convert T_sub_KTB using 1
    constructor <;> intro h <;> contrapose! h
    · exact absurd (h (by tauto)) id
    · intro h
      have := @completeness_T
      apply_assumption
      apply this
      intro F v hv w
      simp +decide [forces]
      exact fun h => ⟨w, hv w, h⟩
  -- Step 3: Chain □φ → φ and φ → ◇φ via cut
  convert cut hT hPhiDia using 1

/-!
## § 11. The 5 Axiom: The Euclidean Property and S5

The 5 axiom (◇φ → □◇φ) expresses that what's possible is necessarily possible.
Semantically, it says the accessibility relation is Euclidean:
if R(x,y) and R(x,z), then R(y,z).

### Why 5 is powerful

Combined with reflexivity (T), the 5 axiom alone gives equivalence relations.
This means S5 = T + 5, and we don't need separate B and 4 axioms.

The proof:
1. **Reflexive + Euclidean → Symmetric**: R(x,y) and R(x,x) give R(y,x)
2. **Reflexive + Euclidean → Transitive**: From R(x,y) and R(y,z):
   by symmetry R(y,x), then Euclidean on R(y,x) and R(y,z) gives R(x,z)

### Euclidean frames without reflexivity

K5 (just the 5 axiom, no T) gives the logic of Euclidean frames.
These frames can have isolated worlds (with no successors), unlike
serial or reflexive frames. K5 is sound and complete for Euclidean frames.

### The KD45 system

KD45 = D + 4 + 5 is the logic of serial, transitive, Euclidean frames.
It is important in epistemic logic as a model of belief (as opposed to knowledge):
- Agents' beliefs are consistent (D: seriality)
- Positive introspection (4: transitivity)
- Negative introspection (5: Euclidean property)

But agents may have false beliefs, since seriality doesn't imply reflexivity.
In contrast, S5 (with reflexivity/T) models knowledge: agents only know truths.
-/

/-- The S5 axiom set equals T + 5. -/
theorem S5_eq_T_union_5 : S5Axioms = TAxioms ∪ K5Axioms := rfl

/-!
## § 12. Counting the 16 Logics: Why Not More?

With 5 axiom schemas {T, B, 4, D, 5}, there are 2^5 = 32 possible subsets.
Here is the complete accounting of which subsets collapse.

### Subsets that reduce to existing logics

**T absorbs D** (7 redundancies):
- {T, D} = KT, {T, B, D} = KTB, {T, 4, D} = S4
- {T, 5, D} = S5, {T, B, 4, D} = S5, {T, B, 5, D} = S5
- {T, 4, 5, D} = S5, {T, B, 4, 5, D} = S5

**T + 5 forces equivalence** (collapses to S5):
- {T, 5} = S5, {T, B, 5} = S5, {T, 4, 5} = S5, {T, B, 4, 5} = S5

**B + 5 forces transitivity** (1 redundancy):
- {B, 4, 5} = KB5 (since B + 5 already implies 4)

**D + B + trans forces equivalence** (2 redundancies):
- {D, B, 4} = S5 (since serial + symmetric + transitive = equivalence)
- {D, B, 5} = S5 (since B + 5 → 4, then D + B + 4 = S5)
- {D, B, 4, 5} = S5

### Final tally

32 total subsets − 16 redundancies = **16 distinct logics**.
-/

end Modal
