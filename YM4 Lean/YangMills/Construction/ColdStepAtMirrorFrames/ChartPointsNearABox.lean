import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
def shiftCoordinates (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (Δ : StepVariable (finiteCells F)) :
    F.Site F.depth → Fin 4 → imaginaryQuaternions :=
  fun x i => w x i + stepCoordinates Δ x i
def CoordinatesCloseOnBall (L : ℕ) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ) (θ : ℝ)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) : Prop :=
  ∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
    fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
    ‖(w (fineBondAt Y h o i).1 i : ℍ[ℝ]) - w' (fineBondAt Y' h o i).1 i‖ ≤ θ
def ballChordBonds (F : BlockFrame) (Y : F.Cell) (r : ℕ) : Finset ↥(chordBonds (finiteCells F)) :=
  open Classical in Finset.univ.filter fun b => cellSupDist (enclosingCell b.1.1) Y ≤ r
end ColdStepAtMirrorFrames
end YangMills.Construction
end
