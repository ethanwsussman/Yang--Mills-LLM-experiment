import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.IteratedSmallFieldMeans (smallFormBall)
def MeanIteratesNearIdentity.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ r : ℝ, 0 < r → ∃ ρ : ℝ, 0 < ρ ∧
    ∀ n k : ℕ, 0 < n → 1 ≤ k → ∀ w ∈ smallFormBall L n k ρ, ∀ m < k,
      meanIterate (remainderGaugeField w) m ∈
          fieldsIn L n k m PeriodicLattice.complexGaugeGroup ∧
        ∀ e, Matrices.ComplexMatrix2.operatorNorm (meanIterate (remainderGaugeField w) m e - 1) < r
end YangMills.Construction.RunningCouplingSlope
end
