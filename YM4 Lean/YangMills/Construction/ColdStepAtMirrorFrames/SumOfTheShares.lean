import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def sumCellSharesEqAction : Prop :=
  ∀ (F : BlockFrame) (a : ℝ) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top),
    0 ≤ a → Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    ∑ Y ∈ finiteCells F, minimalCellShare a (finiteCells F) Y V = minimalAction a (finiteCells F) F.top V ∧
    ∑ Y ∈ finiteCells F, cellEnergyShare a Y w V = chartedEnergy a w V
end YangMills.Construction.ColdStepAtMirrorFrames
end
