import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def AxialGaugeBondBound : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (s : ℝ) (r : ℕ), (∀ i, 2 * r + 2 < F.extent i) →
    0 < s → IsSmallCurvature s V → ∀ b : (Fin 4 → ℤ) × Fin 4, BondWithinRadius r b →
      ‖((gaugeTransform (axialGaugeHolonomy V Y) V (Y + siteOfCoords F.top b.1) b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ 3 * r * s
end YangMills.Construction.ColdStepAtMirrorFrames
end
