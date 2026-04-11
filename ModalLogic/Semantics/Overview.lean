/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Semantics Module

This file imports all semantics-related components of the modal logic formalization.

## Contents

- **Semantics**: Kripke frames, models, and forcing relation
- **Soundness**: Soundness theorem (⊢ φ implies ⊨ φ)
- **Correspondence**: Frame properties definable by modal formulas
- **NonDefinable**: Frame properties not definable by modal formulas
-/

import ModalLogic.Semantics.Semantics
import ModalLogic.Semantics.Soundness
import ModalLogic.Semantics.Correspondence
import ModalLogic.Semantics.Undefinability
import ModalLogic.Semantics.Definability
import ModalLogic.Semantics.Paths
import ModalLogic.Semantics.LocalConsequence
import ModalLogic.Semantics.FiniteModelProperty
import ModalLogic.Semantics.Decidability
import ModalLogic.Semantics.DecidabilityMore

/-!
# Kripke Semantics for Modal Logic

This module provides the semantic interpretation of modal logic through Kripke semantics.

## Core Concepts

**Frame**: A directed graph (W, R) where:
- W is a set of worlds (states, points)
- R ⊆ W × W is an accessibility relation

**Model**: A frame plus a valuation V : Nat → Set W that assigns truth values
to propositional variables at each world.

**Forcing Relation**: M, w ⊩ φ means "formula φ is true at world w in model M"
- Defined recursively on formula structure
- Key clause: M, w ⊩ □φ iff for all v with R w v, we have M, v ⊩ φ

## Validity Notions

We define several notions of validity:
- **Model validity**: True at all worlds in a model
- **Frame validity**: True in all models based on that frame
- **Class validity**: True in all frames of a certain class
- **Universal validity**: True in all frames

## Soundness Theorem

**Main Result**: If Γ ⊢ φ then Γ ⊨ φ

Every syntactically derivable formula is semantically valid.
Proved by structural induction on derivations.

## Definability

Some frame properties are definable by modal formulas:
- Reflexivity (T): □φ → φ
- Transitivity (4): □φ → □□φ
- Symmetry (B): φ → □◇φ
- Euclidean (5): ◇φ → □◇φ

Others are not definable (e.g., irreflexivity, asymmetry).
-/
