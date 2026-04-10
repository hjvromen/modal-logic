/-
Copyright (c) 2025 Huub Vromen. All rights reserved.
Author: Huub Vromen

# Modal Logic - Main Entry Point

This is the main entry point for the modal logic formalization.
Import this file to get access to the entire library.
-/

import ModalLogic.Syntax.Overview
import ModalLogic.Semantics.Overview
import ModalLogic.Metatheory.Overview
import ModalLogic.Cube


/-!
# Modal Logic in Lean 4

A complete formalization of basic modal logic (System K) including:

- **Syntax**: Formula type, proof system, derived operators
- **Semantics**: Kripke frames, models, forcing relation
- **Soundness**: Syntactic derivability implies semantic validity
- **Completeness**: Semantic validity implies syntactic derivability
- **Decidability**: Formula membership in maximal consistent sets

## Quick Start

```lean
import ModalLogic

open Modal

-- Define formulas
def p := Form.var 0
def q := Form.var 1

-- Prove theorems
example : ∅ ⊢K (p ⊃ p) := ProofK.identity
example : ∅ ⊢K (□(p ⊃ q) ⊃ (□p ⊃ □q)) := ProofK.kdist
```

## Main Modules

- `ModalLogic.Syntax.*`: Syntax and proof system
- `ModalLogic.Semantics.*`: Kripke semantics
- `ModalLogic.Metatheory.*`: Completeness via canonical models
-/
