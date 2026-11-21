import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
variable {F : BlockFrame}
def BondCount : Prop :=
  ∀ L : ℕ, Odd L → ∃ nb : ℕ, ∀ (F : BlockFrame) (n : ℕ), F.blockSide = L → 2 ≤ n → (∀ i, F.extent i = n) →
    (innerBonds (finiteCells F) F.top).card = 4 * (finiteCells F).card ∧
    (chordBonds (finiteCells F)).card = nb * (finiteCells F).card
end YangMills.Construction.ColdStepAtMirrorFrames
end
