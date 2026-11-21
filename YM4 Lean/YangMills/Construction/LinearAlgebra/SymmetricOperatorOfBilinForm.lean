import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SymmetricOperator
def ExistsUniqueSymmetricOfBilinForm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E),
    ∃! A : E →ₗ[ℝ] E, A.IsSymmetric ∧ ∀ v : E, inner ℝ v (A v) = B v v
def SymmetricEqOfDiagonalEq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A A' : E →ₗ[ℝ] E),
    A.IsSymmetric → A'.IsSymmetric → (∀ v : E, inner ℝ v (A v) = inner ℝ v (A' v)) → A = A'
def SymmetricOperatorOfBilinForm : Prop :=
  ExistsUniqueSymmetricOfBilinForm ∧ SymmetricEqOfDiagonalEq
end YangMills.Construction.SymmetricOperator
