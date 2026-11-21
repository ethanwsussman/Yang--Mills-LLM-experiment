import YangMills.Construction.Towers.CovariantLinearAverages
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace Tower
def StepMapsComplexLinear.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ V ∈ smallComplexFields L n k j,
      (∀ B ∈ complexEdgeForms L n k j,
        complexSmoothingDeriv V B ∈ complexEdgeForms L n k (j + 1) ∧
        ∀ y, contourLogDrift V B y ∈ Matrices.ComplexMatrix2.traceless) ∧
      (∀ B ∈ complexEdgeForms L n k j, ∀ B' ∈ complexEdgeForms L n k j, ∀ c : ℂ,
        complexSmoothingDeriv V (c • B + B') =
          c • complexSmoothingDeriv V B + complexSmoothingDeriv V B' ∧
        contourLogDrift V (c • B + B') = c • contourLogDrift V B + contourLogDrift V B') ∧
      (∀ l : Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
        covDiff V l ∈ complexEdgeForms L n k j ∧
        ∀ y, adjointCubeAverage V l y ∈ Matrices.ComplexMatrix2.traceless) ∧
      ∀ l l' : Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
        (∀ x, l' x ∈ Matrices.ComplexMatrix2.traceless) → ∀ c : ℂ,
        covDiff V (c • l + l') = c • covDiff V l + covDiff V l' ∧
        adjointCubeAverage V (c • l + l') = c • adjointCubeAverage V l + adjointCubeAverage V l'
end Tower
end YangMills.Construction
end
