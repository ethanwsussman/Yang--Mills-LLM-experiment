import YangMills.Construction.ColdStepAtMirrorFrames.FlatChainsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def flatChainEnergyNearCell : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ del C : ℝ, 0 < del ∧ del ≤ 1 ∧ 0 < C ∧ ∃ L₀ : ℕ,
    ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F),
    Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B →
    ∀ (z : F.Cell) (r : ℕ), r ≤ 24 →
      chainEnergyOnCells a B (cellBall z r) ≤ C * Real.exp (-(2 * del * cellSupDist z c.1))
end YangMills.Construction.ColdStepAtMirrorFrames
end
