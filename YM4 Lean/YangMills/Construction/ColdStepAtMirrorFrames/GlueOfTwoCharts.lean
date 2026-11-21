import YangMills.Construction.ColdStepAtMirrorFrames.ChartPointsNearABox
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def TwoChartsGlue : Prop :=
  ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (θ : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions), F.blockSide = F'.blockSide → Odd F.blockSide →
    (∀ i, 2 * r + 2 < F.extent i) → 0 ≤ θ →
    CoordinatesCloseOnBall F.blockSide Y Y' r θ w w' →
    ∃ (Δ : StepVariable (finiteCells F)) (wx : F.Site F.depth → Fin 4 → imaginaryQuaternions),
      (∀ b, ‖Δ b‖ ≤ θ) ∧ (∀ b, b ∉ ballChordBonds F Y r → Δ b = 0) ∧
      (∀ b ∈ chordBonds (finiteCells F), wx b.1 b.2 = shiftCoordinates w Δ b.1 b.2) ∧
      ∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube F.blockSide →
        wx (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i
end YangMills.Construction.ColdStepAtMirrorFrames
end
