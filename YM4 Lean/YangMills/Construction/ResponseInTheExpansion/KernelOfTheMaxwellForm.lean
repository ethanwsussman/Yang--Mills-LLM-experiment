import YangMills.Construction.ResponseInTheExpansion.MaxwellFormOfTheChain
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
def maxwellKernelBoundsAt : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∀ (k N : ℕ) [NeZero N], Tb.n₀ ≤ N →
    (∀ b b' : TorusFields.TorusBond N,
      WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k b b' =
        WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k b' b) ∧
    (∀ (u : TorusFields.TorusSite N) (b b' : TorusFields.TorusBond N),
      WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k (b.1 + u, b.2) (b'.1 + u, b'.2) =
        WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k b b') ∧
    (∀ b b' : TorusFields.TorusBond N,
      WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k
          (-(b.1 + TorusFields.unitStep N b.2), b.2) (-(b'.1 + TorusFields.unitStep N b'.2), b'.2) =
        WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k b b') ∧
    (∀ b b' : TorusFields.TorusBond N,
      |WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k b b'| ≤
        C * Real.exp (-(c * (TorusFields.supDist b.1 b'.1 : ℝ)))) ∧
    ∀ (m : ℕ) [NeZero m], N ≤ m → ∀ (μ ν : Fin 4) (w : Fin 4 → ℤ), (∀ i, 4 * |w i| ≤ (N : ℤ)) →
      |WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k
          ((0 : TorusFields.TorusSite N), μ) (TorusFields.siteOfInt w, ν) -
        WeightedResponses.maxwellKernel Tb.coupling (Tb.stepParameters y).side k
          ((0 : TorusFields.TorusSite m), μ) (TorusFields.siteOfInt w, ν)| ≤ C * Real.exp (-(c * (N : ℝ)))
def maxwellKernelBoundsStatement : Prop := HoldsOnParameterFamilies maxwellKernelBoundsAt
end YangMills.Construction.ResponseInTheExpansion
end
