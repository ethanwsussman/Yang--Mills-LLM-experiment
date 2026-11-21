import YangMills.Construction.SummableBoundsOfTheFlow.AdmittedObservables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusComparison
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
structure IsShortPairing (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) {ι : Type}
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F'))) : Prop where
  isBoxPairing : IsBoxPairing Y Y' q j j'
  short_offsets : ∀ i, ∃ (h o : Fin 4 → ℤ) (k : Fin 4), (∀ l, 2 * |h l| ≤ q) ∧ o ∈ centredCube F.blockSide ∧
    (j i).1 = fineBondAt Y h o k ∧ (j' i).1 = fineBondAt Y' h o k
end YangMills.Construction.TorusComparison
end
