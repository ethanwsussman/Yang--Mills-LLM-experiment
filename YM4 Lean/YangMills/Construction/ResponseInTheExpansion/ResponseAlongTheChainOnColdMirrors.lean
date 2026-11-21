import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open TorusFields TorusLumps WeightedResponses
open Classical
variable {ℓ : TorusLumps.StepParameters}
def sampledLevelField (k M N : ℕ) (u : MarkedSample ℓ (k + M + M) N) :
    TorusField (fineSide ℓ.side M (fineSide ℓ.side M N)) :=
  topField ℓ k _ (sampleBelow ℓ k M _ (sampleBelow ℓ (k + M) M N u))
end YangMills.Construction.ResponseInTheExpansion
end
