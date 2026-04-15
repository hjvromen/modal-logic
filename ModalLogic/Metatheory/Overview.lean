/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Metatheory Module

This file imports all metatheory-related components of the modal logic formalization.

## Contents

- **Maximal**: Maximal consistent sets and Lindenbaum's lemma
- **MaximalHelpers**: Helper lemmas for maximal consistent sets
- **Canonical**: Canonical model construction and truth lemma
- **CompletenessCube**: Completeness for the classical cube (K, KT, KB, K4, KTB, S4, KB4, S5)
- **CompletenessKDKB**: Completeness for KD and KB
- **CompletenessD5**: Completeness for KD5, KD45, KDB, KD4, K45, KB5
- **CompletenessOverview**: Documentation of the completeness proof strategy

## Additional Metatheory (not imported here to avoid circular dependencies)

- **Interpolation** (`ModalLogic.Metatheory.Interpolation`): Craig interpolation
  and Beth definability for K (fully proved). Imports `Overview.lean` and adds
  V-bisimulation theory, product model construction, canonical V-bisimulation,
  the Craig interpolation theorem, and Beth definability.
-/

import ModalLogic.Metatheory.Maximal
import ModalLogic.Metatheory.MaximalHelpers
import ModalLogic.Metatheory.Canonical
import ModalLogic.Metatheory.CompletenessCube
import ModalLogic.Metatheory.CompletenessKDKB
import ModalLogic.Metatheory.CompletenessD5
import ModalLogic.Metatheory.CompletenessOverview

/-!
# Metatheory of Modal Logic

This module provides the metatheoretic results for modal logic, primarily
soundness and completeness theorems for all 16 normal modal logics.

## Canonical Model Method

Completeness is established via the **canonical model method**:

1. Assume a formula φ is not provable (⊬ φ)
2. Show {¬φ} is consistent
3. Extend to a maximal consistent set via **Lindenbaum's lemma** (using Zorn's lemma)
4. Construct the **canonical model** where worlds are maximal consistent sets
5. Prove the **truth lemma**: w ⊩ ψ iff ψ ∈ w
6. Obtain a countermodel, so φ is not valid (⊭ φ)

## Coverage

Completeness is proven for all 16 distinct normal modal logics:

| Logic | Axioms | Frame Class | File |
|-------|--------|-------------|------|
| K | ∅ | All frames | `Canonical.lean` |
| KT | T | Reflexive | `Canonical.lean` |
| S4 | T+4 | Refl+Trans | `Canonical.lean` |
| S5 | T+B+4 | Equivalence | `Canonical.lean` |
| KD | D | Serial | `CompletenessKDKB.lean` |
| KB | B | Symmetric | `CompletenessKDKB.lean` |
| K4 | 4 | Transitive | `CompletenessCube.lean` |
| K5 | 5 | Euclidean | `CompletenessCube.lean` |
| KTB | T+B | Refl+Symm | `CompletenessCube.lean` |
| KB4 | B+4 | Symm+Trans | `CompletenessCube.lean` |
| KD5 | D+5 | Serial+Euclid | `CompletenessD5.lean` |
| KD45 | D+4+5 | Serial+Trans+Euclid | `CompletenessD5.lean` |
| KDB | D+B | Serial+Symm | `CompletenessD5.lean` |
| KD4 | D+4 | Serial+Trans | `CompletenessD5.lean` |
| K45 | 4+5 | Trans+Euclid | `CompletenessD5.lean` |
| KB5 | B+5 | Symm+Euclid | `CompletenessD5.lean` |

## Craig Interpolation

Craig interpolation for K is fully proved in `ModalLogic.Metatheory.Interpolation`.
The file includes V-bisimulation theory, product model construction, canonical
V-bisimulation (zig/zag), and the complete Craig interpolation theorem
(`craig_interpolation`) together with Beth definability (`beth_definability`).
All results are sorry-free.
-/
