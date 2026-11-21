import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMembers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ConvexClassClosure : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ : ℝ) (d : ι → ι → ℝ), 0 < ρ → 0 < m → 0 ≤ κ →
    IsPseudoMetricOnBonds d → (∀ b b', 0 ≤ d b b') →
    IsConvexClassMember ρ m κ d (fun η => ∑ b, 2 * m * ‖η b‖ ^ 2) ∧
    (∀ (P Q : BondField ι → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 → IsConvexClassMember ρ m κ d P →
      IsConvexClassMember ρ m κ d Q → IsConvexClassMember ρ m κ d fun η => t * P η + (1 - t) * Q η) ∧
    ∀ (P : BondField ι → ℝ) (Λ : Finset ι), IsConvexClassMember ρ m κ d P →
      IsConvexClassMember ρ m κ d fun η => P (restrictToSupport Λ η) + ∑ b ∈ Finset.univ \ Λ, 2 * m * ‖η b‖ ^ 2
end YangMills.Construction.ColdStepAtMirrorFrames
end
