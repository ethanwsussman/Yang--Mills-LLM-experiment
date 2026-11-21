import YangMills.Construction.ClusterExpansionOfAStep.ConvexMeasureOfASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
def TorusLumps.StepParameters.bondWeightBound (ℓ : TorusLumps.StepParameters) : ℝ :=
  ℓ.blockBondBound * (∑' k : ℤ, Real.exp (-(ℓ.rt / 2 * |(k : ℝ)|))) ^ 4
namespace ClusterExpansionOfAStep
open StepSettings
def FreeBondWeightsSummable : Prop :=
  ∀ (R : StepSetup), 0 < R.params.rt → ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n) (b₀ : s.free),
    ∑ b, Real.exp (-(2 * R.params.rt * s.bondDist b b₀)) ≤ R.params.bondWeightBound
end ClusterExpansionOfAStep
end YangMills.Construction
end
