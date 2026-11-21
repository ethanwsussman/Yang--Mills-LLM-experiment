import YangMills.Construction.SummableBoundsOfTheFlow.MixturesOfTwoLevels
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceAtParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames TorusFields WeightedResponses TwoLevelMixtures
namespace LevelComparisons
def responsesAreInterpResponsesStatement : Prop :=
  EventuallyOrdered fun T => ∀ [NeZero T.L], ∃ C : ℝ, 0 < C ∧ ∀ (t n : ℕ) [NeZero n] (c : TorusBond n), 64 ≤ n →
    IsInterpResponse T.a T.L t 0 c (fun b => responseKernel T.a T.ρA T.L t b c) ∧
    IsInterpResponse T.a T.L t 1 c (fun b => responseKernel T.a T.ρA T.L (t + 1) b c) ∧
    ∀ b : TorusBond (n * T.L), |responseKernel T.a T.ρA T.L (t + 1) b c| ≤
      C * Real.exp (-(T.chainParams.κ₂ * bondSiteDist T.L b c.1))
end LevelComparisons
end YangMills.Construction
end
