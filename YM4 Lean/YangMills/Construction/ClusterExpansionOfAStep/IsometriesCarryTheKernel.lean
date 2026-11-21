import YangMills.Construction.ClusterExpansionOfAStep.BasesAtABlock
import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusFields
def TorusIsometry.scaledLift (L : ℕ) (g : TorusIsometry) : TorusIsometry :=
  ⟨g.axisPerm, g.axisSign, fun i => (L : ℤ) * g.offset i, g.axisSign_unit⟩
end YangMills.Construction.TorusFields
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
def IsometriesPreserveAveragedKernel : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (x : ℝ) (n : ℕ) [NeZero n], ℓ.n₀ ≤ n →
    ∀ (g : TorusIsometry) (W W' : TorusField (n * ℓ.side)) (V V' : TorusField n),
    (g.scaledLift ℓ.side).Transports W W' → g.Transports V V' →
    averagedKernel ℓ x (fineLevelField ℓ n W') (coarseLevelField ℓ n V') =
      averagedKernel ℓ x (fineLevelField ℓ n W) (coarseLevelField ℓ n V)
end YangMills.Construction.TorusLumps
end
