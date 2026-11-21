import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.FullSpace
def CovariantStepComplexLinear : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j < k →
    ∀ V ∈ smallComplexFields L k j,
      (∀ B ∈ complexEdgeForms (meshAt L k j),
        complexSmoothingDeriv V B ∈ complexEdgeForms (meshAt L k (j + 1)) ∧
        ∀ y, contourLogDrift V B y ∈ Matrices.ComplexMatrix2.traceless) ∧
      (∀ B ∈ complexEdgeForms (meshAt L k j), ∀ B' ∈ complexEdgeForms (meshAt L k j),
        ∀ c : ℂ,
          complexSmoothingDeriv V (c • B + B') =
            c • complexSmoothingDeriv V B + complexSmoothingDeriv V B' ∧
          contourLogDrift V (c • B + B') = c • contourLogDrift V B + contourLogDrift V B') ∧
      (∀ f : Vertex L k j → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        covDiff V f ∈ complexEdgeForms (meshAt L k j) ∧
        ∀ y, adjointCubeAverage V f y ∈ Matrices.ComplexMatrix2.traceless) ∧
      (∀ f f' : Vertex L k j → Matrices.ComplexMatrix2,
        (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        (∀ x, f' x ∈ Matrices.ComplexMatrix2.traceless) →
        ∀ c : ℂ,
          covDiff V (c • f + f') = c • covDiff V f + covDiff V f' ∧
          adjointCubeAverage V (c • f + f') =
            c • adjointCubeAverage V f + adjointCubeAverage V f')
end YangMills.Construction.Tower.FullSpace
end
