import YangMills.Construction.ColdChainAtEveryLevel.PropertiesOfTheColdChainForm
import YangMills.Construction.ColdStepAtMirrorFrames.AxialRotationsOfATop
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.WeightedResponses
open BlockAverages ColdStepAtMirrorFrames
def axialGaugeNearOneStatement : Prop :=
  ∀ (F : BlockFrame) (V : F.GaugeField F.top) (Y : F.Cell) (s : ℝ) (r : ℕ), (∀ i, 2 * r + 2 < F.extent i) → 0 ≤ s →
    (∀ (c : Fin 4 → ℤ) (i l : Fin 4), i < l → WithinRadius r c → WithinRadius r (c + Pi.single i 1) →
      WithinRadius r (c + Pi.single l 1) → WithinRadius r (c + Pi.single i 1 + Pi.single l 1) →
      plaquetteDefect V (Y + siteOfCoords F.top c, i, l) ≤ s) →
    ∀ b : (Fin 4 → ℤ) × Fin 4, BondWithinRadius r b →
      ‖((gaugeTransform (axialGaugeHolonomy V Y) V (Y + siteOfCoords F.top b.1) b.2 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        3 * r * s
end YangMills.Construction.WeightedResponses
end
