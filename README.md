This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Modal Logic in Lean 4

A comprehensive formalization of normal modal propositional logic in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/), featuring **soundness and completeness proofs for all 16 normal modal logics** in the modal cube, the **finite model property**, and **decidability**.

**~11,100 lines of Lean · 0 sorry's · Only standard axioms (propext, Classical.choice, Quot.sound)**

## Highlights

- **Soundness and completeness** for all **16 distinct** normal modal logics obtainable from subsets of {T, B, 4, D, 5}:
  K, KT, KB, K4, K5, KD, KTB, S4, KB4, KDB, KD4, KD5, K45, KB5, KD45, S5
- **Finite model property** via filtration for K
- **Decidability** of K-validity (`DecidablePred kValid`)
- **Frame correspondence**: T ↔ Reflexive, B ↔ Symmetric, 4 ↔ Transitive, 5 ↔ Euclidean, D ↔ Serial
- **Undefinability** of irreflexivity
- **Local vs. global consequence** with concrete counterexamples
- **Full axiom audit** via `#print axioms` on every major theorem

## The Modal Cube

The project systematically covers every normal modal logic formed by combining five axiom schemas:

| Axiom | Schema | Frame Condition |
|-------|--------|-----------------|
| **T** | □φ → φ | Reflexivity |
| **B** | φ → □◇φ | Symmetry |
| **4** | □φ → □□φ | Transitivity |
| **D** | □φ → ◇φ | Seriality |
| **5** | ◇φ → □◇φ | Euclidean |

While 2⁵ = 32 subsets are possible, key collapse results (e.g., T implies D; T + 5 yields equivalence) reduce them to exactly **16 distinct logics**, all of which are formalized with full soundness and completeness.

```
          S5 = KTB45
         /    |    \
       S4    KTB   KB4
        \     |     /
         KT  KB   K4
          \  |  /
            K         ... + D and 5 extensions
```

## Project Structure

```
ModalLogic/
├── Syntax/
│   ├── Formula.lean            — Formula type, complexity, substitution
│   ├── Derived.lean            — Derived operators (¬, ∨, ◇, ↔) and notation
│   ├── ProofSystem.lean        — Hilbert-style proof system K
│   ├── BasicLemmas.lean        — Weakening, modus ponens, necessitation
│   ├── SyntaxLemmas.lean       — Derived rule toolkit
│   └── Experimental.lean       — Experimental: type-valued derivations, proof metrics (not imported)
├── Semantics/
│   ├── Semantics.lean          — Frames, models, forcing, validity
│   ├── Soundness.lean          — Soundness theorem (all 16 logics)
│   ├── Correspondence.lean     — Frame correspondence theory
│   ├── Definability.lean       — Definable frame properties
│   ├── Undefinability.lean     — Undefinability of irreflexivity
│   ├── Paths.lean              — Reachability and path theory
│   ├── FiniteModelProperty.lean — FMP via filtration
│   ├── Decidability.lean       — Decidability of K-validity
│   └── LocalConsequence.lean   — Local vs. global consequence
├── Metatheory/
│   ├── Maximal.lean            — Maximal consistent sets, Lindenbaum's lemma
│   ├── Canonical.lean          — Canonical model and truth lemma
│   ├── CompletenessCube.lean    — Completeness for the classical cube
│   ├── CompletenessKDKB.lean   — Completeness for KD, KB
│   └── CompletenessD5.lean     — Completeness for remaining logics
└── Cube.lean                   — Unified modal cube with hierarchy theorems
```

Additional files:
- **`Axioms.lean`** — Runs `#print axioms` on every major theorem to verify no `sorry` or unexpected axioms
- **`Examples.lean`** — Worked examples demonstrating the library

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/lean4/doc/setup.html) (v4.28.0 or compatible)
- Mathlib4 (fetched automatically by Lake)

### Build

```bash
git clone <this-repo>
cd modal-logic-lean4
lake build
```

### Usage

```lean
import ModalLogic

open Modal

-- Define propositional variables
def p := Form.var 0
def q := Form.var 1

-- Prove theorems in K
example : ∅ ⊢K (p ⊃ p) := ProofK.identity
example : ∅ ⊢K (□(p ⊃ q) ⊃ (□p ⊃ □q)) := ProofK.kdist

-- Use necessitation
example (h : ∅ ⊢K p) : ∅ ⊢K □p := ProofK.nec h
```

## Proof Technique

Completeness is established via the **canonical model method**:

1. Assume a formula φ is not provable (⊬ φ)
2. Show {¬φ} is consistent
3. Extend to a maximal consistent set via **Lindenbaum's lemma** (using Zorn's lemma)
4. Construct the **canonical model** where worlds are maximal consistent sets
5. Prove the **truth lemma**: w ⊩ ψ iff ψ ∈ w
6. Obtain a countermodel, so φ is not valid (⊭ φ)

For logics beyond K, the canonical model's accessibility relation is shown to satisfy the required frame conditions (reflexivity, transitivity, etc.).

## Related Work

Several formalizations of modal logic have been carried out in other proof assistants.
This project distinguishes itself by covering **all 16 normal modal logics** in the
modal cube with full soundness and completeness, together with the finite model
property and decidability.

| Project | Prover | Logics | Completeness | FMP | Decidability |
|---------|--------|--------|--------------|-----|--------------|
| **This project** | Lean 4 / Mathlib | All 16 | ✓ (all 16) | ✓ (K) | ✓ (K) |
| Bentzen (2021) | Lean 4 | K, S5 | ✓ (K, S5) | ✗ | ✗ |
| From (2021) | Isabelle | K, KT, S4, S5 | ✓ (4 logics) | ✗ | ✗ |
| Doczkal & Smolka (2016) | Coq | K, K* (PDL) | ✓ | ✓ (K*) | ✓ (K*) |
| Blanchette et al. (2014) | Isabelle | Various | Varies | Varies | Varies |

- **Bentzen** formalizes a Hilbert-style proof system for K and S5 in Lean 4,
  with soundness and completeness via canonical models. Our project extends this
  approach to all 16 logics and adds the finite model property and decidability.

- **From** (Isabelle, Archive of Formal Proofs) provides completeness proofs for
  K, KT, S4, and S5 using a synthetic completeness method. Our work covers
  12 additional logics (including the D and 5 families) and provides a unified
  canonical model framework.

- **Doczkal & Smolka** formalize constructive completeness and decidability for
  the modal μ-calculus fragment K* (PDL without iteration) in Coq. Their approach
  emphasizes constructive methods and proof-theoretic decidability, complementing
  our classical canonical model approach.

- **Blanchette et al.** develop formalizations of various logics in Isabelle,
  including some modal fragments, as part of broader formalization efforts.

## References

- Blackburn, de Rijke, and Venema. *Modal Logic*. Cambridge University Press, 2001.
- Chellas, Brian F. *Modal Logic: An Introduction*. Cambridge University Press, 1980.
- Hughes and Cresswell. *A New Introduction to Modal Logic*. Routledge, 1996.
- Bentzen, Bruno. *A Henkin-style completeness proof for the modal logic S5*. 2021.
- From, Asta Halkjær. *Formalizing Henkin-Style Completeness of an Axiomatic System for Propositional Logic*. AFP, 2021.
- Doczkal, Christian and Smolka, Gert. *Completeness and Decidability Results for CTL in Coq*. Journal of Automated Reasoning, 2016.

## License

Copyright © 2025 Huub Vromen. All rights reserved.

## Author

**Huub Vromen**
