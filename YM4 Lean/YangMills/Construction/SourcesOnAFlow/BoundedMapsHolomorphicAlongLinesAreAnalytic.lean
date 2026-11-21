import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ComplexAnalysis
def BoundedLineHolomorphicIsAnalytic : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : E → F) (U : Set E) (M : ℝ), IsOpen U → (∀ x ∈ U, ‖f x‖ ≤ M) →
    (∀ x ∈ U, ∀ v : E, DifferentiableAt ℂ (fun t : ℂ => f (x + t • v)) 0) → AnalyticOnNhd ℂ f U
end YangMills.Construction.ComplexAnalysis
