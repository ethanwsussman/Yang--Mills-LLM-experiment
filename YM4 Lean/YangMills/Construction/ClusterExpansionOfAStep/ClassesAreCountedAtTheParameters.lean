import YangMills.Construction.ClusterExpansionOfAStep.FreeClassesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterBounds
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.RenormalizationStepParameters
def ClusterSumBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ x : ℝ, y ≤ x →
    ∀ (n : ℕ) [NeZero n] (Y : TorusSite n),
      ∑ θ ∈ supportsAtBlock (T.stepParameters y).side (clusterRange x) Y,
        clusterWeight (T.stepParameters y).side T.gasRate x (clusterRange x) θ *
            ((supportCore (T.stepParameters y).side (clusterRange x) θ).card : ℝ) ^ 4 *
          Real.exp (2 * T.rt * (siteDiameter (supportCore (T.stepParameters y).side (clusterRange x) θ) : ℝ)) ≤
        Real.exp (-(8 * T.gasRate * x))
end YangMills.Construction.ClusterBounds
end
