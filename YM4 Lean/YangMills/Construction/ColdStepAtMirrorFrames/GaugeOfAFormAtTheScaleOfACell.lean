import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def weightedGaugeFixingAtCellScale : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (B : LevelForm F 0) (z : F.Cell) (del : ℝ),
    Odd F.blockSide → IsLargeCubicTorus F →
    0 < del → del ≤ 1 → ∃ φ : F.Site 0 → ℝ, (∀ v, cellAverage φ v = 0) ∧
      Real.sqrt (∑ x ∈ sitesOfCells (finiteCells F) 0, ∑ i : Fin 4,
        (Real.exp (-(del * torusSupDist x z)) * addGradient B (fun y => - φ y) x i) ^ 2) ≤
      C * (F.blockSide : ℝ) ^ F.top * (Real.sqrt (∑ x ∈ sitesOfCells (finiteCells F) 0,
          ∑ e ∈ orientedPlanes,
          (Real.exp (-(del * torusSupDist x z)) * plaquetteCurl B x e.1 e.2) ^ 2) +
        Real.sqrt (∑ y ∈ sitesOfCells (finiteCells F) F.top, ∑ i : Fin 4,
          (Real.exp (-(del * torusSupDist y z)) * iteratedLineAverage B F.top y i) ^ 2))
end YangMills.Construction.ColdStepAtMirrorFrames
end
