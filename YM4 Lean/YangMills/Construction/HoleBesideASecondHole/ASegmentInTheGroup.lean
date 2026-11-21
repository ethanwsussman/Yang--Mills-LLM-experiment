import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.GroupPaths
open YangMills.Construction.BlockAverages
def ExistsPathFromOne : Prop :=
  ∃ Φ : ℝ → UnitQuaternion → UnitQuaternion, (∀ g, Φ 0 g = 1) ∧ (∀ g, Φ 1 g = g) ∧
    (∀ (s : ℝ) (g : UnitQuaternion), 0 ≤ s → s ≤ 1 → ‖(g : ℍ[ℝ]) - 1‖ ≤ 1 / 2 →
      ‖((Φ s g : UnitQuaternion) : ℍ[ℝ]) - (1 + s • ((g : ℍ[ℝ]) - 1))‖ ≤ ‖(g : ℍ[ℝ]) - 1‖ ^ 2) ∧
    (∀ (s s' : ℝ) (g g' : UnitQuaternion), 0 ≤ s → s ≤ 1 → 0 ≤ s' → s' ≤ 1 → ‖(g : ℍ[ℝ]) - 1‖ ≤ 1 / 2 →
      ‖(g' : ℍ[ℝ]) - 1‖ ≤ 1 / 2 →
      ‖((Φ s g : UnitQuaternion) : ℍ[ℝ]) - ((Φ s' g' : UnitQuaternion) : ℍ[ℝ])‖ ≤
        4 * (|s - s'| * ‖(g : ℍ[ℝ]) - 1‖ + ‖(g : ℍ[ℝ]) - (g' : ℍ[ℝ])‖))
end YangMills.Construction.GroupPaths
end
