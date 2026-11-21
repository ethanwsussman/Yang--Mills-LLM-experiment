import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MeanCovariantStepOnForms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → 1 ≤ k → j < k →
    Tower.EventuallyNearIdentity (Tower.fieldSpace L n k j) fun V =>
      (∀ B ∈ Tower.complexEdgeForms L n k j,
        meanCovariantStep V B ∈ Tower.complexEdgeForms L n k (j + 1)) ∧
      (∀ B ∈ Tower.complexEdgeForms L n k j, ∀ B' ∈ Tower.complexEdgeForms L n k j, ∀ z : ℂ,
        meanCovariantStep V (z • B + B') = z • meanCovariantStep V B + meanCovariantStep V B') ∧
      (∀ B ∈ Tower.edgeFormSpace L n k j, meanCovariantStep V B ∈ Tower.edgeFormSpace L n k (j + 1)) ∧
      (∀ B ∈ Tower.edgeFormSpace L n k j, ∀ y,
        Tower.contourLogDrift V B y ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
      (∀ l : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, l x ∈ Matrices.ComplexMatrix2.hermitianTraceless) →
        ∀ y, Tower.adjointCubeAverage V l y ∈ Matrices.ComplexMatrix2.hermitianTraceless) ∧
      (∀ l : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
        ∀ y, Tower.adjointCubeAverage V l y ∈ Matrices.ComplexMatrix2.traceless) ∧
      (∀ l l' : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
        (∀ x, l' x ∈ Matrices.ComplexMatrix2.traceless) → ∀ z : ℂ,
        Tower.adjointCubeAverage V (z • l + l') =
          z • Tower.adjointCubeAverage V l + Tower.adjointCubeAverage V l') ∧
      ∀ l : Tower.Vertex L n k j → Matrices.ComplexMatrix2,
        (∀ x, l x ∈ Matrices.ComplexMatrix2.traceless) →
        meanCovariantStep V (Tower.covDiff V l) =
          Tower.covDiff (normalizedMean V) (Tower.adjointCubeAverage V l)
end YangMills.Construction.RunningCouplingSlope
end
