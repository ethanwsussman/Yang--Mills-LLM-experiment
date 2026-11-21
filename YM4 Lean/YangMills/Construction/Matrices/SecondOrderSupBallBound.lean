import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
noncomputable section
namespace YangMills.Construction.Matrices.GroupLieProduct
def SecondOrderBoundOnSupBall : Prop :=
  ∀ (σ : Type) [Fintype σ] [Nonempty σ] (υ M : ℝ), 0 < υ → 0 ≤ M →
    ∀ (b : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless) (N : (σ → ComplexMatrix2) → ComplexMatrix2),
      IsHolomorphicOnTraceless b Coordinates.ComplexCoordinates.matrixEquiv (supBall σ υ) N →
      (∀ A ∈ supBall σ υ, ComplexMatrix2.operatorNorm (N A) ≤ M) →
      N 0 = 0 →
      (∀ A ∈ tracelessPi σ,
        HasDerivAt (fun z : ℂ => Coordinates.ComplexCoordinates.matrixEquiv (N (z • A))) 0 0) →
      ∀ A ∈ supBall σ υ, ComplexMatrix2.operatorNorm (N A) ≤ M * (υ ^ 2)⁻¹ * supNorm A ^ 2
end YangMills.Construction.Matrices.GroupLieProduct
end
