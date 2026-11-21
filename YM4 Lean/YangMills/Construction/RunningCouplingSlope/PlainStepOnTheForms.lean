import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def MeanDerivOnForms.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k m : ℕ, 0 < n → m < k →
    EventuallyNearIdentity (fieldSpace L n k m) fun V =>
      V ∈ smallComplexFields L n k m ∧
      (∀ c : Edge L n k (m + 1), c.IsPositivelyOriented →
        meanRadius V c = (((meanRadius V c).re : ℝ) : ℂ) ∧ 0 < (meanRadius V c).re ∧
          normalizedMean V c ∈ PeriodicLattice.compactGaugeGroup) ∧
      (∀ B ∈ complexEdgeForms L n k m,
        holLeftDifferential normalizedMean V B ∈ complexEdgeForms L n k (m + 1)) ∧
      (∀ B ∈ complexEdgeForms L n k m, ∀ B' ∈ complexEdgeForms L n k m, ∀ w : ℂ,
        holLeftDifferential normalizedMean V (w • B + B') =
          w • holLeftDifferential normalizedMean V B +
            holLeftDifferential normalizedMean V B') ∧
      (∀ B ∈ edgeFormSpace L n k m, holLeftDifferential normalizedMean V B ∈ edgeFormSpace L n k (m + 1)) ∧
      (∀ (B : Edge L n k m → Matrices.ComplexMatrix2) (c : Edge L n k (m + 1)), c.IsPositivelyOriented →
        leftDifferential normalizedMean V B c = holLeftDifferential normalizedMean V B c) ∧
      ∀ f : Vertex L n k m → Matrices.ComplexMatrix2, (∀ x, f x ∈ Matrices.ComplexMatrix2.traceless) →
        holLeftDifferential normalizedMean V (covDiff V f) =
          covDiff (normalizedMean V) (restrictVertexFunction (m + 1) f)
end YangMills.Construction.RunningCouplingSlope
end
