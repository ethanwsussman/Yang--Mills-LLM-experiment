import YangMills.Construction.RunningCouplingSlope.CoordinatesOfTheStepsOfAChainForm
import Mathlib
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields YangMills.Construction.Conventions
def StepChartHessiansPosDef : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ᶠ V in 𝓝 (trivialField (2 * L ^ n)), ∀ j : ℕ, j < k → (chartHessianAtStep a ρ L n k j V).PosDef
end YangMills.Construction.RunningCouplingSlope
end
