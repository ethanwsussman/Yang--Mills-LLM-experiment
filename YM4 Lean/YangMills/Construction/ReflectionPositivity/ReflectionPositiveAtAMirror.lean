import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror.CoordMirror
variable (D : MirrorData) (S : CoordMirror) (E : Ambient)
def reflectedGramSum (σ : Ambient.separatedAll D E → ℝ) {I : ℕ}
    (X : Fin I → Ambient.FnList D E) (c : Fin I → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
    (Ambient.evalOrZero σ (S.reflectAppend D E (X i) (X j)) : ℂ)
def IsReflectionPositiveFor (σ : Ambient.separatedAll D E → ℝ) : Prop :=
  ∀ (I : ℕ) (X : Fin I → Ambient.FnList D E),
    (∀ i, X i ∈ Ambient.separatedWithin D E (S.upperSide D E)) → ∀ c : Fin I → ℂ,
      (S.reflectedGramSum D E σ X c).im = 0 ∧ 0 ≤ (S.reflectedGramSum D E σ X c).re
end YangMills.Construction.ReflectionPositivity.AxisMirror.CoordMirror
