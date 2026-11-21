import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def CovDiffStepRelations : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ V ∈ smallComplexFields L n k j,
      ∀ f : Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        complexSmoothingDeriv V (covDiff V f) =
          covDiff (PeriodicLattice.complexBlockAverageStep j V)
            (restrictVertexFunction (j + 1) f) ∧
        contourLogDrift V (covDiff V f) =
          adjointCubeAverage V f - restrictVertexFunction (j + 1) f ∧
        covariantSmoothingDeriv V (covDiff V f) =
          covDiff (PeriodicLattice.complexBlockAverageStep j V) (adjointCubeAverage V f)
end Tower
end YangMills.Construction
end
