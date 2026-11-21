import YangMills.Construction.Continuum.AxiomsOfOsterwalderAndSchrader
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
abbrev AdmissibleSeq : Type :=
  {Φ : PosTimeSeq // PosTimeSeq.IsFinitelySupported Φ}
def FlatSequence.reflectionForm (S : FlatSequence) (Φ Ψ : AdmissibleSeq) : ℂ :=
  S.reflectionPairing (fun q => (Φ.1 q).1) fun q => (Ψ.1 q).1
def FlatSequence.reflectionNullSpace (S : FlatSequence) : Set AdmissibleSeq :=
  {Φ | S.reflectionForm Φ Φ = 0}
end YangMills.Construction.ConfigSpace
end
