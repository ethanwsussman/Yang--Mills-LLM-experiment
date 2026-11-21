import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields TorusLumps WeightedResponses
def remainderOneStepStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t, t + 1 ≤ S.data.windowLevel → ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ (Y : TorusSite n) (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage (t + 1)).depth n))
      (e e' : TorusBond n),
    |remainderHessian (S.resp (t + 1)) n Y h e e' - ∑ y ∈ sitesInBlocks Λ.stepParams.side {Y},
        pullbackForm Λ.stepParams.coupling (S.tower.stage t).anchorRadius Λ.stepParams.side (S.tower.stage t).depth
          (n := n) (fun b b' =>
            (blockMean Λ.stepParams.side (S.tower.stage t).depth (n * Λ.stepParams.side) y h -
                blockMean Λ.stepParams.side ((S.tower.stage t).depth + 1) n Y h) *
              shareHessian Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth y b b' +
            remainderHessian (S.resp t) (n * Λ.stepParams.side) y h b b') e e'| ≤
      C 0 * S.coupling t ^ (-(1 / 2) : ℝ) * weightLipschitz Λ.stepParams.side (S.tower.stage (t + 1)).depth h /
        Λ.stepParams.weight (tripleDiam Y e e')
end YangMills.Construction.MomentLaw
end
