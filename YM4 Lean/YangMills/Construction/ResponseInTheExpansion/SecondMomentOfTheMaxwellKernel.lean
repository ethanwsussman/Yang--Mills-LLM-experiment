import YangMills.Construction.ResponseInTheExpansion.KernelOfTheCurvature
import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
def MaxwellKernelSecondMomentAt : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N → ∀ (P : Fin 4 → ℝ) (μ ν : Fin 4),
    |(1 / 2 : ℝ) * (∑ x : TorusFields.TorusSite N,
        WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k ((0 : TorusFields.TorusSite N), μ) (x, ν) *
        (∑ i, P i * (LinearResponse.torusDisplacement (0 : TorusFields.TorusSite N) x i +
          ((if i = ν then 1 else 0) - (if i = μ then 1 else 0)) / 2)) ^ 2) +
      (LinearResponse.sqNorm P * (if μ = ν then 1 else 0) - P μ * P ν)| ≤
    C * LinearResponse.sqNorm P * Real.exp (-(c * (N : ℝ)))
def maxwellKernelSecondMomentStatement : Prop := HoldsOnParameterFamilies MaxwellKernelSecondMomentAt
end YangMills.Construction.ResponseInTheExpansion
end
