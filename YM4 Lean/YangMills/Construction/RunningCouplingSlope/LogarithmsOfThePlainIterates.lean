import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.IteratedAveragesOfSmallRegularFields
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MeanIterateLogarithms : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n k : ℕ, 0 < n → 1 ≤ k →
    ∀ v ∈ Tower.IteratedSmallFieldMeans.smallFormBall L n k ρ,
      (∀ j ≤ k, ∃ A ∈ Tower.complexEdgeForms L n k j,
        meanIterate (Tower.remainderGaugeField v) j = PeriodicLattice.expTwist A (fun _ => 1) ∧
          Tower.maxOperatorNorm A ≤
            ENNReal.ofReal (10 * Tower.meshAt L k j * (Tower.maxOperatorNorm v).toReal)) ∧
      (∀ j < k, meanIterate (Tower.remainderGaugeField v) j ∈ Tower.smallComplexFields L n k j) ∧
      ∀ j < k, ∀ c : Tower.Edge L n k (j + 1),
        meanRadius (meanIterate (Tower.remainderGaugeField v) j) c ≠ 0 ∧
          ‖(meanRadius (meanIterate (Tower.remainderGaugeField v) j) c)⁻¹‖ ≤ 2
end YangMills.Construction.RunningCouplingSlope
end
