import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators Matrices Conventions
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries)
open Tower.LeftChartFields (scalarCoords)
def unitCoeffForm (L n k j : ℕ) (ι : Fin 3 × PositiveEdge L n k j) : Edge L n k j → ComplexMatrix2 :=
  open Classical in (edgePauliCoordinates L n k j).ofCoeffs (Pi.single ι 1)
def StepAndNoiseKernelsNearIdentity : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∃ r : ℝ, 0 < r ∧ ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ U : Edge L n k 0 → ComplexMatrix2,
      (∀ j < k, meanIterate U j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
        ∀ b, ComplexMatrix2.operatorNorm (meanIterate U j b - 1) < r) →
      ∀ j < k, meanCovariantStep (meanIterate U j) 0 = 0 ∧
        ∀ (ι' : Fin 3 × PositiveEdge L n k (j + 1)) (ι : Fin 3 × PositiveEdge L n k j),
          meanStepKernel L n k U j ι' ι = pauliCoeff ι'.1
            (((L : ℝ)⁻¹ • meanCovariantStep (meanIterate U j) (unitCoeffForm L n k j ι)) ι'.2.1)) ∧
    ∀ ρ : ℝ, 0 < ρ →
      (∀ v ∈ (complexEdgeForms L n k 0 : Set (Edge L n k 0 → ComplexMatrix2)),
        maxOperatorNorm v < ENNReal.ofReal ρ → ∀ j < k,
          meanIterate (remainderGaugeField v) j ∈ fieldsIn L n k j PeriodicLattice.complexGaugeGroup ∧
            ∀ b, ComplexMatrix2.operatorNorm (meanIterate (remainderGaugeField v) j b - 1) < r) →
      ∀ (a : ℝ) (j : ℕ), j ≤ k → ∀ ι' ι,
        HolomorphicInEntries scalarCoords (complexEdgeForms L n k 0 : Set _) ρ
          fun v => noiseCovariance a L n k (remainderGaugeField v) j ι' ι
end YangMills.Construction.RunningCouplingSlope
end
