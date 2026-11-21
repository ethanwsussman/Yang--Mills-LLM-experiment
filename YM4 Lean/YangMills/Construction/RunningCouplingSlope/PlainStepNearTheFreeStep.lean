import YangMills.Construction.RunningCouplingSlope.PlainCovariantMaps
import YangMills.Construction.Towers.StepsOfTheIteratedAveragesNearTheFreeStepsOnASide
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.SmoothingStepsNearFree (MapNormLE distFromOne)
def MeanStepNearFree.Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ n k m : ℕ, 0 < n → m < k →
    ∀ V ∈ fieldsIn L n k m PeriodicLattice.complexGaugeGroup,
      (∀ e, Matrices.ComplexMatrix2.operatorNorm (V e - 1) < ρ) →
      MapNormLE (meshAt L k m) (meshAt L k (m + 1))
        (edgePauliCoordinates L n k m) (edgePauliCoordinates L n k (m + 1))
        (fun B => (L : ℝ)⁻¹ • (meanCovariantStep V B - crossingSmoothing L n k m B))
        (C * distFromOne V)
end RunningCouplingSlope
end YangMills.Construction
end
