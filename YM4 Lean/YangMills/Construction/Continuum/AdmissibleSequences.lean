import YangMills.Construction.Continuum.OperationsOnFunctionsOfSeveralPoints
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
def zeroOfDegree : (n : ℕ) → FnOrScalar n
  | 0 => (0 : ℂ)
  | _ + 1 => fun _ => 0
abbrev PosTimeSeq : Type := (q : ℕ) → flatOffPosTimeAt q
def PosTimeSeq.IsFinitelySupported (Φ : PosTimeSeq) : Prop :=
  {q | (Φ q).1 ≠ zeroOfDegree q}.Finite
end YangMills.Construction.ConfigSpace
end
