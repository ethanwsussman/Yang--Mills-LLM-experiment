import YangMills.Construction.Towers.OneStepOfACriticalBranch
import YangMills.Construction.Towers.PointsAndLogarithmsOfTheChartAtOne
import Mathlib
set_option autoImplicit false
open Set Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace Tower
open Matrices IdentityExpChart Conventions
def IdentityChartOnFields : Prop :=
  ∀ L n k j : ℕ, IsAdmissibleBlockingFactor L → 0 < n → j ≤ k →
    ∀ [Fintype (PositiveEdge L n k j)],
      IsOpen (lieBall (PositiveEdge L n k j) (1 / 2)) ∧
      (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) ∈
        lieBall (PositiveEdge L n k j) (1 / 2) ∧
      identityChartPoint (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement) = trivialField L n k j ∧
      (∀ y ∈ lieBall (PositiveEdge L n k j) (1 / 2),
        identityChartPoint y ∈ fieldSpace L n k j ∧ identityChartLog (identityChartPoint y) = y) ∧
      (∀ A : Set (PositiveEdge L n k j → ComplexMatrix2.LieElement), IsOpen A →
        A ⊆ lieBall (PositiveEdge L n k j) (1 / 2) →
        IsOpenFieldSet PeriodicLattice.compactGaugeGroup (identityChartPoint '' A)) ∧
      Tendsto (identityChartPoint (L := L) (n := n) (k := k) (j := j)) (𝓝 0)
        (𝓝 (trivialField L n k j)) ∧
      Tendsto (identityChartLog (L := L) (n := n) (k := k) (j := j))
        (𝓝[fieldSpace L n k j] trivialField L n k j) (𝓝 0) ∧
      (∀ A ∈ 𝓝 (0 : PositiveEdge L n k j → ComplexMatrix2.LieElement),
        ∃ ε : ℝ, 0 < ε ∧ nearIdentityBall L n k j ε ⊆ identityChartPoint '' A) ∧
      (∀ ε : ℝ, 0 < ε → nearIdentityBall L n k j ε ∈
        𝓝[fieldSpace L n k j] trivialField L n k j) ∧
      (∀ y : PositiveEdge L n k j → ComplexMatrix2.LieElement,
        ofValues y ∈ edgeFormSpace L n k j ∧ formValues (ofValues y) = y) ∧
      ∀ B ∈ edgeFormSpace L n k j, ofValues (formValues B) = B
end Tower
end YangMills.Construction
end
