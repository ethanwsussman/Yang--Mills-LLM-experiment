import YangMills.Construction.ColdChainAtEveryLevel.RotationOfAFramingOfLevelZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.BlockAverages
variable {F : BlockFrame}
def generatorNearBlockMeanStatement : Prop :=
  ∀ (F : BlockFrame) (j : ℕ) (Γ : F.Site j → UnitQuaternion) (X R : F.GaugeField j) (κ : UnitQuaternion)
    (f : F.Site j → ℍ[ℝ]) (fr : F.Site j → UnitQuaternion)
    (y : F.Site (j + 1)) (t E : ℝ), Odd F.blockSide → 0 ≤ t → t ≤ 1 / 8 → 0 ≤ E →
    (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖((pathHolonomy (gaugeTransform Γ X) (refineSite y) (axisPath h π) *
        (pathHolonomy R (refineSite y) (axisPath h π))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ t) →
    ‖((κ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E →
    (∀ h ∈ centredCube F.blockSide, ∀ π : Equiv.Perm (Fin 4),
      ‖(((fr (refineSite y))⁻¹ * pathHolonomy R (refineSite y) (axisPath h π) *
        fr (refineSite y + siteOfCoords j h) : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ E) →
    (∀ h ∈ centredCube F.blockSide, (f (refineSite y + siteOfCoords j h)).re = 0) →
    ‖adjointAction (fr (refineSite y))⁻¹ (coarseGenerator Γ X R κ f y) -
        (1 / (F.blockSide : ℝ) ^ 4) • ∑ h ∈ centredCube F.blockSide,
          adjointAction (fr (refineSite y + siteOfCoords j h))⁻¹ (f (refineSite y + siteOfCoords j h))‖ ≤
      (9 * t + 4 * E) * ((1 / (F.blockSide : ℝ) ^ 4) *
        ∑ h ∈ centredCube F.blockSide, ‖f (refineSite y + siteOfCoords j h)‖)
end YangMills.Construction.BlockAverages
end
