import YangMills.Construction.TwoPoints.FourShapesAndTheShapeConstant
import YangMills.Construction.TwoPoints.TestPlatesAtAWidthAndTheNumbersOfTheGrowthBound
import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TwoPoints
open YangMills.Construction.InfiniteLattice (AmbientSpace)
open YangMills.Construction.TwoPoints.Shapes (shapeConst)
open YangMills.Construction.TwoPoints.TestPlates (plateWidthNorm growthConst decayGrowthConst)
def AxisDecayGrowthAtZero.Statement : Prop :=
  ∀ (M : FixedScale) (S : (AmbientSpace → ℂ) → (AmbientSpace → ℂ) → ℝ) (d₀ : ℝ) (u : ℝ → ℝ)
    (φ : (Fin 2 → ℝ) → ℂ) (r : ℝ),
    IsDisjointForm S → IsAdmissibleForm M S → IsSmallPositiveWith S shapeConst d₀ u →
    φ ∈ transProfiles → φ ≠ 0 → 0 < r → tsupport φ ⊆ {ζ | euclidNorm ζ ≤ r} →
      (∀ w : ℝ, 0 < w → w ≤ min 1 (min r (2 / 5 * d₀)) →
        axisDecayTransform S φ (7 * w) ≤
          growthConst * r ^ 4 * plateWidthNorm w φ ^ 2 * w ^ (-8 : ℤ) * u (5 / 2 * w)) ∧
      (∀ t : ℝ, 0 < t → t ≤ 7 * min 1 (min r (2 / 5 * d₀)) →
        t ^ 8 * axisDecayTransform S φ t ≤
          decayGrowthConst * r ^ 4 *
            (YangMills.Construction.TestFunctions.uniformNorm φ + gradPlaneSup φ) ^ 2 *
            u (5 / 14 * t)) ∧
      Tendsto (fun t : ℝ => t ^ 8 * axisDecayTransform S φ t) (𝓝[>] 0) (𝓝 0)
end YangMills.Construction.TwoPoints
end
