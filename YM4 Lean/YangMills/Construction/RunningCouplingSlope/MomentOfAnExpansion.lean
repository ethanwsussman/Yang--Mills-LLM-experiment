import YangMills.Construction.RunningCouplingSlope.MomentOfATotal
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages RenormalizationStepParameters TorusLumps
namespace RunningCouplingSlope
def CenteredDensityMomentDecay : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (y : ℝ) (t : ℕ) (x : ℝ) (D : TorusFunctional)
      (f : LocalDensity), T.floorMin ≤ y → ColdExpansion (T.stepParameters y) t x D f →
    ∀ (n : ℕ) [NeZero n] (X : imaginaryQuaternions), T.n₀ ≤ n → ‖X‖ = 1 →
      |gaugeTotalMoment (centeredDensityTotal f) n X| ≤ C * Real.exp (-(c * n))
end RunningCouplingSlope
end YangMills.Construction
end
