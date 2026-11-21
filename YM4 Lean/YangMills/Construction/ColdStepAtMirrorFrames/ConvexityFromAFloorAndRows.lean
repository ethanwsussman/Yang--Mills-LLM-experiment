import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def ConvexityOfHessianFloorPlusSmallRows : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ x ℓ₀ κ : ℝ) (d : ι → ι → ℝ)
    (A R : BondField ι → ℝ) (KA KR : ι → ι → ℝ),
    0 < ρ → 0 < x → 0 < ℓ₀ → 0 ≤ κ → (∀ b b', 0 ≤ d b b') →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 A η) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 3 R η) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ u : BondField ι,
      ℓ₀ * ∑ b, ‖u b‖ ^ 2 ≤ secondDerivAlong A η u u) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b b' : ι) (e e' : BondVector),
      |secondDerivAlong A η (bondVariation b e) (bondVariation b' e')| ≤ KA b b' * ‖e‖ * ‖e'‖) →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ (b b' : ι) (e e' : BondVector),
      |secondDerivAlong R η (bondVariation b e) (bondVariation b' e')| ≤ KR b b' * ‖e‖ * ‖e'‖) →
    (∀ b b', KA b b' = KA b' b) → (∀ b b', KR b b' = KR b' b) → (∀ b b', 0 ≤ KR b b') →
    (∀ b, ∑ b', KA b b' * (Real.exp (2 * κ * d b b') - 1) ≤ ℓ₀ / 16) →
    (∀ b, ∑ b', KR b b' * Real.exp (2 * κ * d b b') ≤ x * ℓ₀ / 16) →
    ∃ Φ : BondField ι → ℝ, (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → Φ η = x * A η + R η) ∧
      IsUniformlyConvexDecaying ρ (x * ℓ₀ / 4) κ d Φ (fun b b' => x * KA b b' + KR b b') ∧
      ∀ (b : ι) (e : BondVector),
        bondPartialDeriv Φ b 0 e = x * bondPartialDeriv A b 0 e + bondPartialDeriv R b 0 e
end ColdStepAtMirrorFrames
end YangMills.Construction
end
