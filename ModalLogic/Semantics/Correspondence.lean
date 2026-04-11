import Mathlib.Order.Defs.Unbundled
import Mathlib.Logic.Relation

namespace Modal

structure Frame where
  states : Type _
  rel : states → states → Prop

namespace Frame

variable {f : Frame}

abbrev box (φ : f.states → Prop) (w : f.states) : Prop :=
  ∀ v, f.rel w v → φ v

abbrev diamond (φ : f.states → Prop) (w : f.states) : Prop :=
  ∃ v, f.rel w v ∧ φ v

abbrev impl (φ ψ : f.states → Prop) (w : f.states) : Prop :=
  φ w → ψ w

abbrev conj (φ ψ : f.states → Prop) (w : f.states) : Prop :=
  φ w ∧ ψ w

abbrev neg (φ : f.states → Prop) (w : f.states) : Prop :=
  ¬ φ w

abbrev valid (φ : f.states → Prop) : Prop :=
  ∀ w, φ w

def Reflexive (f : Frame) : Prop :=
  ∀ (x : f.states), f.rel x x

def Symmetric (f : Frame) : Prop :=
  ∀ {x y : f.states}, f.rel x y → f.rel y x

def Transitive (f : Frame) : Prop :=
  ∀ {x y z : f.states}, f.rel x y → f.rel y z → f.rel x z

def Euclidean (f : Frame) : Prop :=
  ∀ {x y z : f.states}, f.rel x y → f.rel x z → f.rel y z

def Serial (f : Frame) : Prop :=
  ∀ (w : f.states), ∃ v, f.rel w v

theorem T_of_Reflexive (hrefl : Reflexive f)
    (φ : f.states → Prop) (w : f.states) :
    box φ w → φ w :=
  fun h => h w (hrefl w)

theorem Four_of_Transitive (htrans : Transitive f)
    (φ : f.states → Prop) (w : f.states) :
    box φ w → box (box φ) w :=
  fun h u hwu v huv => h v (htrans hwu huv)

theorem B_of_Symmetric (hsym : Symmetric f)
    (φ : f.states → Prop) (w : f.states) :
    φ w → box (diamond φ) w :=
  fun hφ v hwv => ⟨w, hsym hwv, hφ⟩

theorem Five_of_Euclidean (heuc : Euclidean f)
    (φ : f.states → Prop) (w : f.states) :
    diamond φ w → box (diamond φ) w :=
  fun ⟨u, hwu, hφu⟩ v hwv => ⟨u, heuc hwv hwu, hφu⟩

theorem D_of_Serial (hser : Serial f)
    (φ : f.states → Prop) (w : f.states) :
    box φ w → diamond φ w := by
  intro h; obtain ⟨v, hv⟩ := hser w; exact ⟨v, hv, h v hv⟩

end Frame
end Modal
