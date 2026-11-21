import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GradientFromOscillation
open YangMills.Construction.ColdStepAtMirrorFrames
def BondGradBoundOfOscillation : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : BondField ι → ℝ) (ρ τ e M : ℝ) (b : ι),
    ContDiff ℝ 2 G → 0 < τ → τ < ρ → 0 ≤ M →
    (∀ ζ ζ' : BondField ι, (∀ c, ‖ζ c‖ < ρ) → (∀ c, ‖ζ' c‖ < ρ) → (∀ c, c ≠ b → ζ c = ζ' c) →
      |G ζ - G ζ'| ≤ e) →
    (∀ ζ : BondField ι, (∀ c, ‖ζ c‖ < ρ) → ∀ X : BondVector,
      |secondDerivAlong G ζ (bondVariation b X) (bondVariation b X)| ≤ M * ‖X‖ ^ 2) →
    ∀ η : BondField ι, (∀ c, ‖η c‖ < ρ) → bondGradNorm G b η ≤ e / (2 * τ) + 4 * M * τ
end YangMills.Construction.GradientFromOscillation
end
