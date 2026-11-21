import YangMills.Construction.HoleBesideASecondHole.TreeGaugeOfAField
import YangMills.Construction.ColdChainAtEveryLevel.LevelRecursionNearACell
import YangMills.Construction.ColdChainAtEveryLevel.PinnedRelativeGauge
import YangMills.Construction.ColdChainAtEveryLevel.UnitPartsOfQuaternions
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def linkGap {j : ℕ} (T R : F.GaugeField j) : F.Site j → Fin 4 → ℝ :=
  fun x i => normSubOne (T x i * (R x i)⁻¹)
def balancedLinks {j : ℕ} (T R : F.GaugeField j) (kR : F.Site (j + 1) → UnitQuaternion) :
    F.Site (j + 1) → UnitQuaternion :=
  fun y => kR y * balancingGauge T R y
theorem distFromOne_sq (g : UnitQuaternion) : normSubOne g ^ 2 = 2 - 2 * ((g : ℍ[ℝ])).re := by apply _root_.YangMills.Construction.GaugeFixing.norm_coe_sub_one_sq <;> assumption
def gaugedOneStepComparisonStatement : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (F : BlockFrame) (j : ℕ) (T R : F.GaugeField j)
    (kR : F.Site (j + 1) → UnitQuaternion) (T' R' : F.GaugeField (j + 1)) (b : F.Site (j + 1) × Fin 4) (t ε : ℝ),
    Odd F.blockSide → j + 1 ≤ F.top → 0 ≤ t → 0 ≤ ε → (F.blockSide : ℝ) * t ≤ c₀ → ε ≤ c₀ →
    BoundedOnAdjacentBlocks (linkGap T R) b t →
    (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      normSubOne (pathHolonomy R (refineSite b.1) (bondContour F.blockSide h π b.2) *
        (polarUnit (contourAverage R b))⁻¹) ≤ ε) →
    1 / 2 ≤ ‖gaugedContourAverage T (balancedLinks T R kR) b‖ ∧
    normSubOne (T' b.1 b.2 * (R' b.1 b.2)⁻¹) ≤
      normSubOne (bondMisfit T (balancedLinks T R kR) T' b * (bondMisfit R kR R' b)⁻¹) +
        lineBlockAverage (linkGap T R) b +
        C * ((F.blockSide : ℝ) * t) * ((F.blockSide : ℝ) * t + ε)
end YangMills.Construction.BlockAverages
end
