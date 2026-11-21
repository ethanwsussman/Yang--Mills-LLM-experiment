import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
open YangMills.Construction.Matrices
def FibreMinimisersNearOne : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ F : (Edge L n k i → ComplexMatrix2) → ℝ,
      (∃ O : Set (Edge L n k i → ComplexMatrix2), IsOpenNhdOfOne O ∧
        IsAnalyticFieldFunction O F) →
      leftGradient (fieldSpace L n k i) (fun U => (F U : ℂ)) (trivialField L n k i) = 0 →
      (∀ ξ ∈ edgeFormSpace L n k i, linearSmoothing L n k i ξ = 0 → ξ ≠ 0 →
        0 < leftSecondDeriv F (trivialField L n k i) ξ ξ) →
      ∃ (O : Set (Edge L n k i → ComplexMatrix2)) (ε : ℝ)
        (p : (Edge L n k (i + 1) → ComplexMatrix2) → Edge L n k i → ComplexMatrix2),
        IsFibreCriticalSection F O ε p
end YangMills.Construction.Tower
end
