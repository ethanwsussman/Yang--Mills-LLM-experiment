import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ResponseInTheExpansion.ImageResponseIsAMeanOfTheGas
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.StepGas YangMills.Construction.TorusLumps YangMills.Construction.TorusFields YangMills.Construction.WeightedResponses YangMills.Construction.BlockAverages
def centredGasBlockAgreementStatement : Prop :=
  HoldsAtEveryStep fun _ R A => R.IsWellPosed →
    ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (G : GasGround R n) (G' : GasGround R n') (Y : TorusSite n)
      (Y' : TorusSite n') (m : ℕ)
      (h : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n))
      (h' : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n')) (s₂ : ℝ),
      G.IsAdmissibleGround → G'.IsAdmissibleGround → R.params.n₀ ≤ n → R.params.n₀ ≤ n' →
      GroundsAgreeNear G G' Y Y' m →
      (clusterRange R.nextCoupling : ℝ) / 64 ≤ m → WeightsAgreeAt R.params.side (R.depth + 1) Y Y' h h' →
      ∑ o ∈ centredCube R.params.side, recordedSiteScore A G (fineSite R.params.side Y 0 o) ≤ s₂ →
      |(gasBlockMean A G Y h - gasBlockMean A (coldCaseGround R (trivialField n)) Y h) -
          (gasBlockMean A G' Y' h' - gasBlockMean A (coldCaseGround R (trivialField n')) Y' h')| ≤
        (1 + s₂) * Real.exp (-R.params.decayRate * m) * weightNorm R.params.side (R.depth + 1) h
end YangMills.Construction.ResponseInTheExpansion
end
