import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsAndSetsAtPositiveDistance
import YangMills.Construction.TorusOrFourSpace.RadiusPartitionOfUnityAndTheNumberTheta
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.BallsToSeparated
open Kind
def TorusBoundFromBallsOfOneRadius : Prop :=
  ∀ (D : Params) (θ : RadiusRatio) (P : TorusPartitionChoice D θ) (n : ℕ), 2 ≤ n →
    ∀ d c : ℝ, 0 < d → 0 ≤ c →
    ∀ Ψ : sepC1Tuples D torus n → ℝ,
      IsMultilinearOn D torus (sepC1Tuples D torus n) Ψ →
      (∀ g : sepC1Tuples D torus n,
        g.1 ∈ lipTuplesSpacedInBalls D torus n d (ballRadius D θ torus) →
          ENNReal.ofReal |Ψ g| ≤ ENNReal.ofReal c * ∏ i, sharpNormQ D torus (g.1 i)) →
      ∀ h : sepC1Tuples D torus n, ENNReal.ofReal d ≤ supportGap D torus h.1 →
        ENNReal.ofReal |Ψ h| ≤
          ENNReal.ofReal (thetaNumber P torus ^ n * c) * ∏ i, sharpNormQ D torus (h.1 i)
end YangMills.Construction.PeriodicSpace.BallsToSeparated
