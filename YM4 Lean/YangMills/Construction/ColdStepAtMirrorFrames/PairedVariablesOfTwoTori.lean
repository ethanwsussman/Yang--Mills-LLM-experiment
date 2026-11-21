import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
variable {F F' : BlockFrame}
def AreOffsetPaired {ι : Type} (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (j : ι → ↥(chordBonds (finiteCells F)))
    (j' : ι → ↥(chordBonds (finiteCells F'))) : Prop :=
  ∀ i, ∃ (g u : Fin 4 → ℤ) (k : Fin 4), u ∈ centredCube F.blockSide ∧ WithinRadius q g ∧
    (j i).1 = fineBondAt Y g u k ∧ (j' i).1 = fineBondAt Y' g u k
def PairedCoordinatesAgree : Prop :=
  ∀ (F F' : BlockFrame) (Y : F.Cell) (Y' : F'.Cell) (q : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (j : ι → ↥(chordBonds (finiteCells F))) (j' : ι → ↥(chordBonds (finiteCells F')))
    (ξ : BondField ι) (h o : Fin 4 → ℤ) (i : Fin 4),
    F.blockSide = F'.blockSide → Odd F.blockSide → (∀ i, 2 * q + 2 < F.extent i) →
    (∀ i, 2 * q + 2 < F'.extent i) →
    Function.Injective j → Function.Injective j' → AreOffsetPaired Y Y' q j j' → WithinRadius q h →
    o ∈ centredCube F.blockSide →
    (fineBondAt Y h o i ∈ chordBonds (finiteCells F) ↔ fineBondAt Y' h o i ∈ chordBonds (finiteCells F')) ∧
      stepCoordinates (pushforwardField j ξ) (fineBondAt Y h o i).1 i =
        stepCoordinates (pushforwardField j' ξ) (fineBondAt Y' h o i).1 i
end ColdStepAtMirrorFrames
end YangMills.Construction
end
