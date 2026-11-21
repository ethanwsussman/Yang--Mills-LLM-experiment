import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusFields TorusLumps RenormalizationStepParameters SlopeCoefficient
namespace RunningCouplingSlope
def IsInvariantFunctionalAbove (ℓ : StepParameters) (D : TorusFunctional) : Prop :=
  ∀ n [NeZero n], ℓ.n₀ ≤ n → Measurable (D n) ∧ (∀ W, 0 ≤ D n W) ∧
    (∀ (g : TorusSite n → BlockAverages.UnitQuaternion) (W : TorusField n), D n (gaugeTransform g W) = D n W) ∧
    ∀ (g : TorusIsometry) (W W' : TorusField n), g.Transports W W' → D n W' = D n W
def ColdDensitiesHaveZeroCoefficient : Prop :=
  ∀ (T : ParameterAssignment) (y : ℝ) (t : ℕ) (x ρ : ℝ) (D : TorusFunctional) (f : LocalDensity), T.Admissible →
    (T.stepParameters y).Admissible → 0 < ρ → ρ ≤ 1 →
    IsInvariantFunctionalAbove (T.stepParameters y) D → ColdExpansion (T.stepParameters y) t x D f →
    HasSlopeCoefficient Filter.atTop (centeredDensityTotal f) 0 ∧
      HasSlopeCoefficient Filter.atTop (atMinimizer T.coupling ρ T.side t (centeredDensityTotal f)) 0
end RunningCouplingSlope
end YangMills.Construction
end
