import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses YangMills.Construction.BlockAverages
def gasBlockMeanBoundStatement : Prop :=
  HoldsAtEveryStep fun T R A => ∀ (n : ℕ) [NeZero n] (G : GasGround R n) (Y : TorusSite n)
    (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)), G.IsAdmissibleGround →
    |gasBlockMean A G Y h| ≤
      ((R.params.side : ℝ) ^ 4 * (A.responseParams.C₀ + Real.exp (-(6 * T.gasRate * R.coupling))) +
          ∑ o ∈ centredCube R.params.side, recordedSiteScore A G (fineSite R.params.side Y 0 o) +
        8 * R.params.coupling * (2 + Real.exp (-(6 * T.gasRate * R.coupling)))) *
          weightNorm R.params.side R.depth h
end YangMills.Construction.ResponseInTheExpansion
end
