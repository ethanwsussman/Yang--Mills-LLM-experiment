import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace TorusLumps
def ClusterSumBound : Prop :=
  ∀ (ℓ : StepParameters) (c : ℝ), ℓ.Admissible → 0 < c → ℓ.RangeFloor c → ∀ x : ℝ, ℓ.y₁ ≤ x →
    ∀ (n : ℕ) [NeZero n] (Y : TorusFields.TorusSite n),
      ∑ θ ∈ supportsAtBlock ℓ.side (clusterRange x) Y,
        clusterWeight ℓ.side c x (clusterRange x) θ *
          ((supportCore ℓ.side (clusterRange x) θ).card : ℝ) ^ 4 *
          Real.exp (2 * ℓ.rt * (siteDiameter (supportCore ℓ.side (clusterRange x) θ) : ℝ)) ≤
        Real.exp (-(8 * c * x))
end TorusLumps
end YangMills.Construction
end
