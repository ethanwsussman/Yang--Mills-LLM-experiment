import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Towers.OneStepOfACriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower
def AxialGaugeOfProlongation : Prop :=
  ∀ L n k i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < n → i < k →
    ∀ (b : CriticalBranchData L n k) (𝒰 : Set (Edge L n k i → Matrices.ComplexMatrix2)) (ε : ℝ)
      (p : (Edge L n k (i + 1) → Matrices.ComplexMatrix2) → Edge L n k i → Matrices.ComplexMatrix2),
      b.IsCriticalUpTo i → IsFibreCriticalSection (b.gaugeFixedEnergy i) 𝒰 ε p →
        EventuallyNearIdentity (fieldSpace L n k (i + 1)) fun W =>
          IsAxialGaugeAt L n k i (p W) ∧ b.gaugeFixedEnergy i (p W) = b.energy i (p W)
end YangMills.Construction.Tower
end
