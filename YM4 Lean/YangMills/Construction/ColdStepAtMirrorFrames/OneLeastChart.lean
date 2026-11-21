import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def MinimizingChartUnique : Prop :=
  ∀ (F : BlockFrame) (a ρ N0 s : ℝ) (V : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions),
    Odd F.blockSide → (∀ i, 2 ≤ F.extent i) →
    ρ ≤ 1 → HasColdMinimizer a ρ N0 s (finiteCells F) V → IsMinimizingChart a (finiteCells F) V ρ w →
    (∀ w' : F.Site F.depth → Fin 4 → imaginaryQuaternions, IsMinimizingChart a (finiteCells F) V ρ w' → w' = w) ∧
    IsCold (finiteCells F) F.depth (s / 8) (chartedField w V)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
