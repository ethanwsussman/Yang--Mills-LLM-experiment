import YangMills.Construction.LimitTheorem.ConditionsAtGivenConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensities
def ContractionFunctionalReconstructs : Prop :=
  ∀ σ : SeparatedTuples.TupleFunctional, σ.IsAdmissiblyContinuous →
    ReflectionPositivity.ContractionFunctionals.IsAdmissible σ →
    (∀ r, LimitTheorem.IsHyperoctahedralMotion r → LimitTheorem.IsMotionInvariant σ r) →
    LimitTheorem.ReconstructionProperties σ
end YangMills.Construction.TotalDensities
end
