import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.TorusFields YangMills.Construction.StepGas YangMills.Construction.StepSettings YangMills.Construction.BlockAverages
def gasBlockMeanDecorrelationStatement : Prop :=
  HoldsAtEveryStep fun T R A =>
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n)
      (Y' : TorusSite n') (m : ℕ) (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
      (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → GroundsAgreeNear G G' Y Y' m → 16 * R.frameReach ≤ m →
      WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h' →
      |gasBlockMean A G Y h - gasBlockMean A G' Y' h'| ≤
        ((R.params.side : ℝ) ^ 4 + ∑ o ∈ centredCube R.params.side,
            recordedSiteScore A G (fineSite R.params.side Y 0 o) + 8 * R.params.coupling) *
          (Real.exp (-(15 / 16 * R.params.rt * m / 2 ^ 5)) +
            Real.exp (-(2 * T.gasRate * R.coupling) - R.params.rt * m / 2 ^ 8)) *
          weightNorm R.params.side R.depth h
end YangMills.Construction.ResponseInTheExpansion
end
