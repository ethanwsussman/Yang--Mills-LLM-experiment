import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GroupPaths
open YangMills.Construction.BlockAverages
def PlaquetteAlongPathsBound : Prop :=
  ∀ Φ : ℝ → UnitQuaternion → UnitQuaternion,
    (∀ (s : ℝ) (g : UnitQuaternion), 0 ≤ s → s ≤ 1 → ‖(g : ℍ[ℝ]) - 1‖ ≤ 1 / 2 →
      ‖((Φ s g : UnitQuaternion) : ℍ[ℝ]) - (1 + s • ((g : ℍ[ℝ]) - 1))‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ ^ 2) →
    ∀ (s₁ s₂ s₃ s₄ : ℝ) (g₁ g₂ g₃ g₄ : UnitQuaternion), 0 ≤ s₁ → s₁ ≤ 1 → 0 ≤ s₂ → s₂ ≤ 1 → 0 ≤ s₃ → s₃ ≤ 1 →
      0 ≤ s₄ → s₄ ≤ 1 →
      ‖(g₁ : ℍ[ℝ]) - 1‖ ≤ 1 / 2 → ‖(g₂ : ℍ[ℝ]) - 1‖ ≤ 1 / 2 → ‖(g₃ : ℍ[ℝ]) - 1‖ ≤ 1 / 2 →
      ‖(g₄ : ℍ[ℝ]) - 1‖ ≤ 1 / 2 →
      ‖((Φ s₁ g₁ * Φ s₂ g₂ * (Φ s₃ g₃)⁻¹ * (Φ s₄ g₄)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        ‖((g₁ * g₂ * g₃⁻¹ * g₄⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ +
          (|s₂ - s₁| * ‖(g₂ : ℍ[ℝ]) - 1‖ + |s₃ - s₁| * ‖(g₃ : ℍ[ℝ]) - 1‖ + |s₄ - s₁| * ‖(g₄ : ℍ[ℝ]) - 1‖) +
          11 * (‖(g₁ : ℍ[ℝ]) - 1‖ ^ 2 + ‖(g₂ : ℍ[ℝ]) - 1‖ ^ 2 + ‖(g₃ : ℍ[ℝ]) - 1‖ ^ 2 + ‖(g₄ : ℍ[ℝ]) - 1‖ ^ 2)
end YangMills.Construction.GroupPaths
end
