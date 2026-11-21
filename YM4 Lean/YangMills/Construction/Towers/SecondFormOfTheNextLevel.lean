import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def NextLevelHessian.Statement : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ (b : CriticalBranchData L n k) (𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2)) (ε : ℝ)
      (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
      b.IsCriticalUpTo i → IsFibreCriticalSection (b.gaugeFixedEnergy i) 𝒰 ε p →
        (∃ 𝒲 : Set (Edge L n k (i + 1) → Matrices.ComplexMatrix2), IsOpenNhdOfOne 𝒲 ∧
          IsAnalyticFieldFunction 𝒲 fun W => b.gaugeFixedEnergy i (p W)) ∧
        EventuallyNearIdentity (fieldSpace L n k (i + 1))
          (fun W => 0 ≤ b.gaugeFixedEnergy i (p W)) ∧
        b.gaugeFixedEnergy i (p (trivialField L n k (i + 1))) = 0 ∧
        leftGradient (fieldSpace L n k (i + 1)) (fun W => (b.gaugeFixedEnergy i (p W) : ℂ))
          (trivialField L n k (i + 1)) = 0 ∧
        (∀ B ∈ edgeFormSpace L n k (i + 1),
          0 ≤ leftSecondDeriv (fun W => b.gaugeFixedEnergy i (p W))
            (trivialField L n k (i + 1)) B B) ∧
        (∀ B ∈ edgeFormSpace L n k (i + 1),
          (∀ B' ∈ edgeFormSpace L n k (i + 1), leftSecondDeriv (fun W => b.gaugeFixedEnergy i (p W))
            (trivialField L n k (i + 1)) B B' = 0) ↔ IsClosedEdgeForm B) ∧
        (∀ B ∈ edgeFormSpace L n k (i + 1),
          IsLeast {r | ∃ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ = B ∧
              r = b.stepQuadratic i ξ}
            (leftSecondDeriv (fun W => b.gaugeFixedEnergy i (p W))
              (trivialField L n k (i + 1)) B B)) ∧
        ∀ B ∈ edgeFormSpace L n k (i + 1), ∀ ξ : Edge L n k i → Matrices.ComplexMatrix2,
          (ξ ∈ edgeFormSpace L n k i ∧ linearSmoothing L n k i ξ = B ∧
              b.stepQuadratic i ξ = leftSecondDeriv (fun W => b.gaugeFixedEnergy i (p W))
                (trivialField L n k (i + 1)) B B) ↔
            ξ = leftDifferential p (trivialField L n k (i + 1)) B
end YangMills.Construction.Tower
end
