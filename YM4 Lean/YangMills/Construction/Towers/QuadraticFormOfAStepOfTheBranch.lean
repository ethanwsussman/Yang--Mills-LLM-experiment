import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.FamiliesOfCriticalBranches
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def StepQuadraticForm : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ b : CriticalBranchData L n k, b.IsCriticalUpTo i →
      (∃ U : Set (Edge L n k i → Matrices.ComplexMatrix2), IsOpenNhdOfOne U ∧
        IsAnalyticFieldFunction U (b.gaugeFixedEnergy i)) ∧
      b.gaugeFixedEnergy i (trivialField L n k i) = 0 ∧
      leftGradient (fieldSpace L n k i) (fun V => (b.gaugeFixedEnergy i V : ℂ))
        (trivialField L n k i) = 0 ∧
      (∀ ξ ∈ edgeFormSpace L n k i, leftSecondDeriv (b.gaugeFixedEnergy i)
        (trivialField L n k i) ξ ξ = b.stepQuadratic i ξ) ∧
      ∀ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ = 0 → ξ ≠ 0 →
        0 < b.stepQuadratic i ξ
end YangMills.Construction.Tower
end
