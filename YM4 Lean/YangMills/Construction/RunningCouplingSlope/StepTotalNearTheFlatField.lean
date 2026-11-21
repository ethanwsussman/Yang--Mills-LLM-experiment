import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.RunningCouplingSlope.ExponentOfAStepAlongACurve
import YangMills.Construction.RunningCouplingSlope.LaplaceOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
open YangMills.Construction.BlockAverages YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.SlopeCoefficient YangMills.Construction.LaplaceAsymptotics
namespace YangMills.Construction.RunningCouplingSlope
def stepTotalNearTrivialStatement : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (y : ℝ) (S : StepSetup), T.floorMin ≤ y → S.OnParameters T y →
    ∀ (n : ℕ) [NeZero n] (c : Fin 2 → TorusBond n) (X : Fin 2 → imaginaryQuaternions), T.n₀ ≤ n →
      ContDiffAt ℝ 2
        (fun τ : Fin 2 → ℝ => stepGaugeTotal T.coupling T.ρA T.side S.depth n (perturb c X τ (trivialField n))) 0 ∧
      ContDiffAt ℝ 2 (fun τ : Fin 2 → ℝ => densityAtMinimizer S n (perturb c X τ (trivialField n))) 0 ∧
      ∃ κ : ℝ, ∀ᶠ τ in 𝓝 (0 : Fin 2 → ℝ),
        stepGaugeTotal T.coupling T.ρA T.side S.depth n (perturb c X τ (trivialField n)) +
            densityAtMinimizer S n (perturb c X τ (trivialField n)) =
          κ + gaussianLogValue (chartEnergyAlongCurve S n c X) (exponentRemainderAlongCurve S n c X) τ -
            haarGapSumAlongCurve S n c X τ
end YangMills.Construction.RunningCouplingSlope
end
