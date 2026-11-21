import YangMills.Construction.ColdStepAtMirrorFrames.KernelsOfTheChartEnergy
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def CellEnergyShareLocal : Prop :=
  ∀ (a : ℝ) (L : ℕ) (c : ColdChainParameters), 1 ≤ a → Odd L → 2 ^ 40 ≤ L → c.Admissible a L →
    ∃ C : ℝ, 0 < C ∧
      ∀ (F F' : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
        (w' : F'.Site F'.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top)
        (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ), 1 ≤ r → IsBlockTorus L F →
        IsBlockTorus L F' → F'.depth = F.depth → IsAdmissibleChartPoint L c.σA w V →
        IsAdmissibleChartPoint L c.σA w' V' →
        AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
        (∀ (h o : Fin 4 → ℤ) (i : Fin 4), WithinRadius r h → o ∈ centredCube L →
          fineBondAt Y h o i ∈ chordBonds (finiteCells F) →
          w (fineBondAt Y h o i).1 i = w' (fineBondAt Y' h o i).1 i) →
        |cellEnergyShare a Y w V - cellEnergyShare a Y' w' V'| ≤ C * Real.exp (-(c.δ₁ * r))
end ColdStepAtMirrorFrames
end YangMills.Construction
end
