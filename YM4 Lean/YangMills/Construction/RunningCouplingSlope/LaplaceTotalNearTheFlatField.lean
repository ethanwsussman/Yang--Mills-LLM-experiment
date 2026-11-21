import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.LaplaceAsymptotics
def laplaceRemainderNearTrivialStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (y : ℝ) (R : StepSetup), T.floorMin ≤ y → R.OnParameters T y →
    ∀ (n k : ℕ) [NeZero n] (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), T.n₀ ≤ n →
      n ≤ 4 * R.frameReach + 5 →
      ∃ κ : ℝ, ∀ᶠ τ in 𝓝 (0 : Fin k → ℝ), laplaceRemainder R n (perturb c X τ (trivialField n)) =
        κ + logCutoffIntegral T.ballRadius T.cutoff R.coupling (chartEnergyAlongCurve R n c X)
          (exponentRemainderAlongCurve R n c X) τ
end YangMills.Construction.RunningCouplingSlope
end
