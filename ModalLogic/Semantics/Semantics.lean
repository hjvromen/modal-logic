import ModalLogic.Semantics.Correspondence

inductive BasicModal.Form : Type where
  | bot  : BasicModal.Form
  | var  : Nat → BasicModal.Form
  | and  : BasicModal.Form → BasicModal.Form → BasicModal.Form
  | impl : BasicModal.Form → BasicModal.Form → BasicModal.Form
  | box  : BasicModal.Form → BasicModal.Form
  deriving DecidableEq, Repr

namespace BasicModal.Form

def neg (φ : Form) : Form := impl φ bot
def disj (φ ψ : Form) : Form := impl (neg φ) ψ
def dia (φ : Form) : Form := neg (box (neg φ))
def top : Form := neg bot

end BasicModal.Form

namespace Modal

def forces (F : Frame.{0}) (V : Nat → F.states → Prop) :
    F.states → BasicModal.Form → Prop
  | _, .bot      => False
  | w, .var n    => V n w
  | w, .and φ ψ  => forces F V w φ ∧ forces F V w ψ
  | w, .impl φ ψ => forces F V w φ → forces F V w ψ
  | w, .box φ    => ∀ v, F.rel w v → forces F V v φ

end Modal
