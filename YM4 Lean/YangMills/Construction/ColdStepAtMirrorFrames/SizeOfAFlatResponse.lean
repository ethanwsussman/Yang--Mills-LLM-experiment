import YangMills.Construction.ColdStepAtMirrorFrames.SumAgainstThreeFlatResponses
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
variable {F : BlockFrame}
def axialResponseDecay : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ del C : ℝ, 0 < del ∧ del ≤ 1 ∧ 0 < C ∧ ∃ L₀ : ℕ,
    ∀ (F : BlockFrame) (c : F.Site F.top × Fin 4) (B : FormChain F) (W : LevelForm F F.depth),
      Odd F.blockSide → L₀ ≤ F.blockSide → IsLargeCubicTorus F → IsFlatChain a c B →
      IsAxialResponse c B W → ∀ b ∈ chordBonds (finiteCells F),
        |W b.1 b.2| ≤ C * (F.blockSide : ℝ) ^ 3 * Real.exp (-(del * cellSupDist (enclosingCell b.1) c.1))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
