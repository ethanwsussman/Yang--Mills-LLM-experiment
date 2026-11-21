import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def CurlSizeBound : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ C : ℝ, 0 < C ∧ ∃ L₀ : ℕ,
    ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F),
    Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B →
    ∀ (Y : F.Cell) (p : F.Site F.depth) (e : Fin 4 × Fin 4), e ∈ orientedPlanes →
      cellSupDist (enclosingCell p) Y ≤ 2 →
      |plaquetteCurl (B F.depth) p e.1 e.2| ≤
        C * (F.blockSide : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.sqrt (chainEnergyOnCells a B (cellBall Y 24))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
