import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def CovariantStepRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ V ∈ smallComplexFields L k j,
      ∀ f : Vertex L k j → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        complexSmoothingDeriv V (covDiff V f) =
          covDiff (smoothingMap L k j V) (restrictVertexFunction (meshAt L k (j + 1)) f) ∧
        contourLogDrift V (covDiff V f) =
          adjointCubeAverage V f - restrictVertexFunction (meshAt L k (j + 1)) f ∧
        covariantSmoothingDeriv V (covDiff V f) =
          covDiff (smoothingMap L k j V) (adjointCubeAverage V f)
end YangMills.Construction.Tower.FullSpace
end
