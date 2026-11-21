import YangMills.Construction.Continuum.AdmissibleSequences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def linCombAt (c c' : ℂ) :
    {n : ℕ} → FnOrScalar n → FnOrScalar n → FnOrScalar n
  | 0, φ, φ' => (c * (show ℂ from φ) + c' * (show ℂ from φ') : ℂ)
  | _ + 1, φ, φ' => fun y => c * φ y + c' * φ' y
def IsLinComb (c c' : ℂ) (Φ Φ' Φ'' : PosTimeSeq) : Prop :=
  ∀ q : ℕ, (Φ'' q).1 = linCombAt c c' (Φ q).1 (Φ' q).1
def IsZeroSeq (Φ : PosTimeSeq) : Prop :=
  ∀ q : ℕ, (Φ q).1 = zeroOfDegree q
def LinCombClosure : Prop :=
  (∃ Φ : PosTimeSeq, PosTimeSeq.IsFinitelySupported Φ ∧ IsZeroSeq Φ) ∧
    ∀ (c c' : ℂ) (Φ Φ' : PosTimeSeq),
      PosTimeSeq.IsFinitelySupported Φ → PosTimeSeq.IsFinitelySupported Φ' →
        ∃ Φ'' : PosTimeSeq,
          PosTimeSeq.IsFinitelySupported Φ'' ∧ IsLinComb c c' Φ Φ' Φ''
end YangMills.Construction.ConfigSpace
end
