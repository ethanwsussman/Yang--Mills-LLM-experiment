import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace LinearConstraint
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
def absDetOfMap (A : E →ₗ[ℝ] F) : ℝ :=
  Real.sqrt (LinearMap.det (LinearMap.adjoint A ∘ₗ A))
def normSqForm (l : E →ₗ[ℝ] F) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((innerₗ F).compl₁₂ l l)
end LinearConstraint
end YangMills.Construction
end
