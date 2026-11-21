import YangMills.Construction.ColdStepAtMirrorFrames.CompatibleLocalFamiliesGlue
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open ColdStepAtMirrorFrames WeightedResponses BlockMeans
theorem coldRegimeEstimates_holds (hJ : EventuallyInParametersCombines)
    (h₁ : SmoothIncrementExpectations) (h₂ : ScoreRemainderDecay) (h₃ : weightedFrameSharesStatement)
    (h₄ : conditionalMeanStatement) (h₅ : meanRemainderStatement)
    (h₆ : blockRemainderMeanStatement) (h₇ : dilationIdentity)
    (h₈ : dilationRemainderSecondOrderStatement) (h₉ : dilationRemainderLocalityStatement)
    (h₁₀ : dilationRemainderAtCurvatureStatement)
    (h₁₁ : ResponseInTheExpansion.framesEquivariantStatement) (h₁₂ : ResponseInTheExpansion.gaussianMomentApproxStatement)
    (h₁₃ : ResponseInTheExpansion.smoothIncrementBounds) (h₁₄ : blockSumExpectationNearValueStatement) :
    coldRegimeEstimatesStatement := by
  obtain ⟨join, weaken⟩ := hJ
  obtain ⟨Cf, -, hb⟩ := h₁₃
  have h₁₃' : EventuallyInParameters fun T => ∃ C : ℝ, ResponseInTheExpansion.smoothIncrementBoundsAt T C :=
    weaken _ _ (fun T _ h => ⟨_, h⟩) hb
  refine weaken _ _ (fun T _ h => ?_) (join _ _ h₁ (join _ _ h₂ (join _ _ h₃ (join _ _ h₄ (join _ _ h₅
    (join _ _ h₆ (join _ _ h₇ (join _ _ h₈ (join _ _ h₉ (join _ _ h₁₀ (join _ _ h₁₁ (join _ _ h₁₂
      (join _ _ h₁₃' h₁₄)))))))))))))
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, m, o, q⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, o, m, q⟩
end YangMills.Construction.ResponseInTheExpansion
end
