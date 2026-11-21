import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.IteratedSmallFieldMeans (HolomorphicInEntries)
open YangMills.Construction.Tower.LeftChartFields (scalarCoords)
def MeanIteratesHolomorphicOfNear.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ r : ℝ, 0 < r ∧ ∀ ρ : ℝ, 0 < ρ → ∀ n k : ℕ, 0 < n → 1 ≤ k →
    (∀ w ∈ (complexEdgeForms L n k 0 : Set (Edge L n k 0 → Matrices.ComplexMatrix2)),
      maxOperatorNorm w < ENNReal.ofReal ρ → ∀ m < k,
      meanIterate (remainderGaugeField w) m ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup ∧
        ∀ e, Matrices.ComplexMatrix2.operatorNorm (meanIterate (remainderGaugeField w) m e - 1) < r) →
    (∀ m ≤ k, ∀ e : Edge L n k m,
      HolomorphicInEntries Coordinates.ComplexCoordinates.matrixEquiv (complexEdgeForms L n k 0 : Set _) ρ
        fun w => meanIterate (remainderGaugeField w) m e) ∧
    (∀ i' i, HolomorphicInEntries scalarCoords (complexEdgeForms L n k 0 : Set _) ρ
      fun w => meanKernelQ L n k (remainderGaugeField w) i' i) ∧
    ∀ i' i, HolomorphicInEntries scalarCoords (complexEdgeForms L n k 0 : Set _) ρ
      fun w => meanKernelR L n k (remainderGaugeField w) i' i
end RunningCouplingSlope
end YangMills.Construction
end
