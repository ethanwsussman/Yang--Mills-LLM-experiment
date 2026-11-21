import YangMills.Construction.ColdStepAtMirrorFrames.ResponsesNearAFlatTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
open YangMills.Construction.BlockAverages BlockOffsets
variable {F : BlockFrame}
def ChartedFieldNearOne : Prop :=
  ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
    (Y : F.Cell) (q s : ℝ) (R : ℕ) (b : F.Site F.depth × Fin 4),
    (∀ i, 2 * R + 2 < F.extent i) → 0 ≤ q → 0 ≤ s → IsNearUniformAbout s R V Y →
    (∀ b', ¬ IsAxialTreeBond b' → ‖w b'.1 b'.2‖ ≤ q) → cellSupDist Y (enclosingCell b.1) + 1 ≤ R →
    distFromOne (chartedField w V b.1 b.2) ≤
      q + 3 * ((cellSupDist Y (enclosingCell b.1) : ℝ) + 1) * s
end YangMills.Construction.ColdStepAtMirrorFrames
end
