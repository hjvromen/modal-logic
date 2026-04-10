import ModalLogic.Metatheory.Maximal

/-!
# Simplified API for Maximal Consistent Sets

This file provides a clean, organized API for working with maximal consistent sets
without introducing custom wrapper types.

## Main Features

- Convenient constructors for maximal sets
- Clean API for decidability and logical operations
- Helper functions for common patterns
- Documentation and examples

## Usage

Import this file to get access to convenient lemmas with descriptive names:
```lean

```
-/

open Classical
open Modal
open BasicModal
open BasicModal.ProofK

noncomputable section

variable {AX : Ctx}

------------------------------------------------------------------------------
-- § 1. Convenience Constructors
------------------------------------------------------------------------------

/--
Convert an existential to a Nonempty type for use with Classical.choice.
-/
private def exists_to_nonempty {α : Type*} {P : α → Prop} (h : ∃ x, P x) :
    Nonempty { x // P x } :=
  let ⟨x, hx⟩ := h
  ⟨⟨x, hx⟩⟩

/--
Construct a maximal consistent set from any semantically consistent axiom system.

**Example:**
```lean
def myWorld (hsem : sem_cons ∅) : { Γ : Ctx // max_ax_consist ∅ Γ } :=
  getMaximalSet ∅ hsem
```
-/
def getMaximalSet (AX : Ctx) (hsem : sem_cons AX) :
    { Γ : Ctx // max_ax_consist AX Γ } :=
  Classical.choice (exists_to_nonempty (max_ax_exists AX hsem))

/--
Extend a consistent set to a maximal one using Lindenbaum's lemma.

**Example:**
```lean
def extend_empty (hsem : sem_cons AX) (hcons : ax_consist AX ∅) :
    { Γ : Ctx // max_ax_consist AX Γ ∧ ∅ ⊆ Γ } :=
  extendToMaximal ∅ hcons
```
-/
def extendToMaximal (Γ : Ctx) (hcons : ax_consist AX Γ) :
    { Γ' : Ctx // max_ax_consist AX Γ' ∧ Γ ⊆ Γ' } :=
  Classical.choice (exists_to_nonempty (lindenbaum AX Γ hcons))

/--
Extract the underlying context from a maximal consistent set witness.

**Example:**
```lean
def myContext (hsem : sem_cons ∅) : Ctx :=
  maximalContext (getMaximalSet ∅ hsem)
```
-/
def maximalContext {AX : Ctx} (w : { Γ : Ctx // max_ax_consist AX Γ }) : Ctx :=
  w.val

/--
Extract the maximality proof from a maximal consistent set witness.
-/
def maximalProof {AX : Ctx} (w : { Γ : Ctx // max_ax_consist AX Γ }) :
    max_ax_consist AX w.val :=
  w.property

------------------------------------------------------------------------------
-- § 2. Decidability and Properties
------------------------------------------------------------------------------

/--
Every formula is decidable in a maximal consistent set.

**Law of Excluded Middle**: For any φ, either φ ∈ Γ or ¬φ ∈ Γ.
-/
theorem maximal_decides (Γ : Ctx) (hmax : max_ax_consist AX Γ) (φ : Form) :
    (φ ∈ Γ) ∨ (∼φ) ∈ Γ :=
  let hcons := max_imp_ax hmax
  ((six AX Γ hcons).mp hmax φ).1

/--
No contradictions in maximal consistent sets.

**Non-Contradiction**: φ and ¬φ cannot both be in Γ.
-/
theorem maximal_no_contradiction (Γ : Ctx) (hmax : max_ax_consist AX Γ) (φ : Form) :
    ¬(φ ∈ Γ ∧ (∼φ) ∈ Γ) :=
  let hcons := max_imp_ax hmax
  ((six AX Γ hcons).mp hmax φ).2

/--
Negation characterization: φ ∉ Γ if and only if ¬φ ∈ Γ.

**Completeness Property**: The absence of φ is equivalent to the presence of ¬φ.
-/
theorem maximal_not_mem_iff (Γ : Ctx) (hmax : max_ax_consist AX Γ) (φ : Form) :
    (φ ∉ Γ) ↔ ((∼φ) ∈ Γ) :=
  max_notiff AX Γ hmax φ

/--
Get the consistency proof from maximality.

Since every maximal consistent set is consistent, we can extract this proof.
-/
theorem maximal_is_consistent (Γ : Ctx) (hmax : max_ax_consist AX Γ) :
    ax_consist AX Γ :=
  max_imp_ax hmax

------------------------------------------------------------------------------
-- § 3. Logical Operations (Convenient Versions)
------------------------------------------------------------------------------

/--
**Modus Ponens**: If (φ ⊃ ψ) ∈ Γ and φ ∈ Γ, then ψ ∈ Γ.
-/
theorem maximal_mp (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ ψ : Form}
    (himp : (φ ⊃ ψ) ∈ Γ) (hφ : φ ∈ Γ) : ψ ∈ Γ :=
  max_imp_2 hmax himp hφ

/--
**Conjunction Introduction**: If φ ∈ Γ and ψ ∈ Γ, then (φ ∧ ψ) ∈ Γ.
-/
theorem maximal_and_intro (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ ψ : Form}
    (hφ : φ ∈ Γ) (hψ : ψ ∈ Γ) : (φ & ψ) ∈ Γ :=
  max_conj_1 hmax ⟨hφ, hψ⟩

/--
**Left Conjunction Elimination**: If (φ ∧ ψ) ∈ Γ, then φ ∈ Γ.
-/
theorem maximal_and_left (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ ψ : Form}
    (hconj : (φ & ψ) ∈ Γ) : φ ∈ Γ :=
  max_conj_2 hmax hconj

/--
**Right Conjunction Elimination**: If (φ ∧ ψ) ∈ Γ, then ψ ∈ Γ.
-/
theorem maximal_and_right (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ ψ : Form}
    (hconj : (φ & ψ) ∈ Γ) : ψ ∈ Γ :=
  max_conj_3 hmax hconj

/--
**Double Negation**: φ ∈ Γ if and only if ¬¬φ ∈ Γ.
-/
theorem maximal_double_neg (Γ : Ctx) (hmax : max_ax_consist AX Γ) (φ : Form) :
    (φ ∈ Γ) ↔ ((∼∼φ) ∈ Γ) :=
  max_dn AX Γ hmax φ

/--
**Implication Introduction**: If (φ ∈ Γ → ψ ∈ Γ), then (φ ⊃ ψ) ∈ Γ.
-/
theorem maximal_imp_intro (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ ψ : Form}
    (h : φ ∈ Γ → ψ ∈ Γ) : (φ ⊃ ψ) ∈ Γ :=
  max_imp_1 hmax h

/--
**Box respects double negation**: If ¬□φ ∈ Γ, then ¬□¬¬φ ∈ Γ.
-/
theorem maximal_box_dn (Γ : Ctx) (hmax : max_ax_consist AX Γ) (φ : Form)
    (h : (∼(□φ)) ∈ Γ) : (∼(□(∼∼φ))) ∈ Γ :=
  max_boxdn AX Γ hmax φ h

------------------------------------------------------------------------------
-- § 4. Finite Provability
------------------------------------------------------------------------------

/--
**Deduction in Maximal Sets**: If a finite list L ⊆ Γ proves φ, and Γ is maximal,
then φ ∈ Γ.

This is the key bridge between syntactic provability and semantic membership.
-/
theorem maximal_proves (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ : Form} {L : List Form}
    (hall : ∀ ψ ∈ L, ψ ∈ Γ) (hprf : ProofK AX (fin_conj L ⊃ φ)) : φ ∈ Γ :=
  exercise1 hmax hall hprf

/--
**Single Formula Deduction**: If ψ ∈ Γ and ψ ⊢ φ, then φ ∈ Γ.

This is a convenient special case of `maximal_proves` for single formulas.
-/
theorem maximal_derives (Γ : Ctx) (hmax : max_ax_consist AX Γ) {φ ψ : Form}
    (hψ : ψ ∈ Γ) (hprf : ProofK AX (ψ ⊃ φ)) : φ ∈ Γ := by
  apply maximal_proves Γ hmax (L := [ψ])
  · intro χ hmem
    rw [List.mem_singleton] at hmem
    rw [hmem]
    exact hψ
  · simp [fin_conj]
    exact cut (mp pl5 phi_and_true) hprf

------------------------------------------------------------------------------
-- § 5. Canonical Model Helpers
------------------------------------------------------------------------------

/--
Type alias for canonical worlds: a world is just a maximal consistent set.
-/
def World (AX : Ctx) := { Γ : Ctx // max_ax_consist AX Γ }

namespace World

/--
Get the underlying context of a world.
-/
def toCtx {AX : Ctx} (w : World AX) : Ctx := w.val

/--
Get the maximality proof of a world.
-/
def isMaximal {AX : Ctx} (w : World AX) : max_ax_consist AX w.val := w.property

/--
Membership in a world - the primary way to check if a formula is in a world.

Use this as `World.mem φ w` or you can write `φ ∈ w.val` if you prefer.
-/
def mem {AX : Ctx} (φ : Form) (w : World AX) : Prop := φ ∈ w.val

-- Note: We intentionally do NOT define a Membership instance here to avoid
-- coercion confusion. Use `World.mem φ w` explicitly.

/--
Decidability for worlds.
-/
theorem decides {AX : Ctx} (w : World AX) (φ : Form) :
    (mem φ w) ∨ (mem (∼φ) w) :=
  maximal_decides w.val w.property φ

/--
Modus ponens for worlds.
-/
theorem mp {AX : Ctx} (w : World AX) {φ ψ : Form}
    (himp : mem (φ ⊃ ψ) w) (hφ : mem φ w) : mem ψ w :=
  maximal_mp w.val w.property himp hφ

/--
Conjunction introduction for worlds.
-/
theorem and_intro {AX : Ctx} (w : World AX) {φ ψ : Form}
    (hφ : mem φ w) (hψ : mem ψ w) : mem (φ & ψ) w :=
  maximal_and_intro w.val w.property hφ hψ

/--
Left conjunction elimination for worlds.
-/
theorem and_left {AX : Ctx} (w : World AX) {φ ψ : Form}
    (hconj : mem (φ & ψ) w) : mem φ w :=
  maximal_and_left w.val w.property hconj

/--
Right conjunction elimination for worlds.
-/
theorem and_right {AX : Ctx} (w : World AX) {φ ψ : Form}
    (hconj : mem (φ & ψ) w) : mem ψ w :=
  maximal_and_right w.val w.property hconj

/--
Double negation for worlds.
-/
theorem double_neg {AX : Ctx} (w : World AX) (φ : Form) :
    (mem φ w) ↔ (mem (∼∼φ) w) :=
  maximal_double_neg w.val w.property φ

/--
Negation characterization for worlds.
-/
theorem not_mem_iff {AX : Ctx} (w : World AX) (φ : Form) :
    (¬(mem φ w)) ↔ (mem (∼φ) w) :=
  maximal_not_mem_iff w.val w.property φ

/--
No contradictions in worlds.
-/
theorem no_contradiction {AX : Ctx} (w : World AX) (φ : Form) :
    ¬(mem φ w ∧ mem (∼φ) w) :=
  maximal_no_contradiction w.val w.property φ

/--
Implication introduction for worlds.
-/
theorem imp_intro {AX : Ctx} (w : World AX) {φ ψ : Form}
    (h : mem φ w → mem ψ w) : mem (φ ⊃ ψ) w :=
  maximal_imp_intro w.val w.property h

/--
Proves a formula in a world from a finite derivation.
-/
theorem proves {AX : Ctx} (w : World AX) {φ : Form} {L : List Form}
    (hall : ∀ ψ ∈ L, mem ψ w) (hprf : ProofK AX (fin_conj L ⊃ φ)) : mem φ w := by
  apply maximal_proves w.val w.property
  · intro ψ hmem
    exact hall ψ hmem
  · exact hprf

/--
Derive a formula in a world from a single premise.
-/
theorem derives {AX : Ctx} (w : World AX) {φ ψ : Form}
    (hψ : mem ψ w) (hprf : ProofK AX (ψ ⊃ φ)) : mem φ w :=
  maximal_derives w.val w.property hψ hprf

end World

------------------------------------------------------------------------------
-- § 6. Usage Examples and Patterns
------------------------------------------------------------------------------

section Examples

-- Assume we have semantic consistency
variable (hsem : sem_cons ∅)

/-- Example: Create a maximal consistent set -/
example : ∃ Γ : Ctx, max_ax_consist ∅ Γ :=
  max_ax_exists ∅ hsem

/-- Example: Every formula is decided in a maximal set -/
example (Γ : Ctx) (hmax : max_ax_consist ∅ Γ) (φ : Form) :
    (φ ∈ Γ) ∨ ((∼φ) ∈ Γ) :=
  maximal_decides Γ hmax φ

/-- Example: Conjunction works as expected -/
example (Γ : Ctx) (hmax : max_ax_consist ∅ Γ) (φ ψ : Form)
    (hφ : φ ∈ Γ) (hψ : ψ ∈ Γ) : (φ & ψ) ∈ Γ :=
  maximal_and_intro Γ hmax hφ hψ

/-- Example: Implication behaves properly -/
example (Γ : Ctx) (hmax : max_ax_consist ∅ Γ) (φ ψ : Form)
    (himp : (φ ⊃ ψ) ∈ Γ) (hφ : φ ∈ Γ) : ψ ∈ Γ :=
  maximal_mp Γ hmax himp hφ

/-- Example: Using the World type with explicit mem -/
example : ∃ w : World ∅, ∀ φ : Form, (World.mem φ w) ∨ (World.mem (∼φ) w) := by
  use getMaximalSet ∅ hsem
  intro φ
  exact World.decides (getMaximalSet ∅ hsem) φ

/-- Example: Chaining logical operations on raw contexts -/
example (Γ : Ctx) (hmax : max_ax_consist ∅ Γ) (φ ψ χ : Form)
    (hφ : φ ∈ Γ) (hψ : ψ ∈ Γ) (himp : ((φ & ψ) ⊃ χ) ∈ Γ) : χ ∈ Γ := by
  have hconj := maximal_and_intro Γ hmax hφ hψ
  exact maximal_mp Γ hmax himp hconj

/-- Example: World operations using explicit mem -/
example (w : World ∅) (φ ψ : Form)
    (hφ : World.mem φ w) (hψ : World.mem ψ w) : World.mem (φ & ψ) w :=
  World.and_intro w hφ hψ

/-- Example: Decidability in worlds -/
example (w : World ∅) (φ : Form) : (World.mem φ w) ∨ (World.mem (∼φ) w) :=
  World.decides w φ

/-- Example: Complex reasoning in worlds -/
example (w : World ∅) (φ ψ χ : Form)
    (hφ : World.mem φ w) (hψ : World.mem ψ w)
    (himp : World.mem ((φ & ψ) ⊃ χ) w) : World.mem χ w := by
  have hconj := World.and_intro w hφ hψ
  exact World.mp w himp hconj

end Examples

end

/-!
## Documentation

### Quick Start
```lean


-- Create a maximal set
def myWorld (hsem : sem_cons ∅) : World ∅ :=
  getMaximalSet ∅ hsem

-- Use decidability
theorem example1 (hsem : sem_cons ∅) (φ : Form) :
    (World.mem φ (myWorld hsem)) ∨ (World.mem (∼φ) (myWorld hsem)) :=
  World.decides (myWorld hsem) φ

-- Chain operations
theorem example2 (w : World ∅) (φ ψ : Form)
    (hφ : World.mem φ w) (hψ : World.mem ψ w) : World.mem (φ & ψ) w :=
  World.and_intro w hφ hψ
```

### API Categories

1. **Constructors** (`§1`):
   - `getMaximalSet`: Create maximal set from semantic consistency
   - `extendToMaximal`: Extend consistent set to maximal
   - `maximalContext`, `maximalProof`: Extract components

2. **Properties** (`§2`):
   - `maximal_decides`: Decidability (excluded middle)
   - `maximal_no_contradiction`: Consistency
   - `maximal_not_mem_iff`: Negation characterization

3. **Logical Operations** (`§3`):
   - `maximal_mp`: Modus ponens
   - `maximal_and_intro/left/right`: Conjunction rules
   - `maximal_imp_intro`: Implication introduction
   - `maximal_double_neg`: Double negation

4. **Provability** (`§4`):
   - `maximal_proves`: General deduction from finite list
   - `maximal_derives`: Single formula deduction

5. **World Type** (`§5`):
   - `World`: Type alias for maximal sets
   - `World.mem`: Explicit membership function
   - `World.decides`, `World.mp`, `World.and_intro`: Logical operations

### Important Note on Membership

We use `World.mem φ w` explicitly instead of `φ ∈ w` to avoid type system confusion.
This is more verbose but much more reliable.

For raw contexts, you can still use `φ ∈ Γ` as usual.

### Design Principles

- **No custom types fighting Lean**: Uses standard `Ctx` and proof terms
- **Descriptive names**: All lemmas have clear, searchable names
- **Convenient API**: Wrappers for common patterns
- **Well-documented**: Examples and usage patterns included
- **Backward compatible**: Doesn't break existing code

### Benefits Over Custom Types

✅ **No universe polymorphism issues**
✅ **No membership synthesis problems**
✅ **No field access errors**
✅ **Works with existing infrastructure**
✅ **Easy to extend and modify**
✅ **Better error messages**
-/
