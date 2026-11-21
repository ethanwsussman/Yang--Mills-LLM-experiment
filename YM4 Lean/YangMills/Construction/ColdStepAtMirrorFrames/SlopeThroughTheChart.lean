import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def DerivThroughChart : Prop :=
  ∃ (C : ℝ) (T : imaginaryQuaternions → BondVector → imaginaryQuaternions), 0 < C ∧
    ∀ (F : BlockFrame) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (G : F.GaugeField F.depth → ℝ),
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
    ContDiffThreeAlongBonds G (chartedField w V) →
    ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector), ‖T (w b.1.1 b.1.2) e‖ ≤ C * ‖e‖ ∧
      fderiv ℝ (readInChart G w V) 0 (bondVariation b e) =
        bondDeriv G (chartedField w V) ![b.1] ![T (w b.1.1 b.1.2) e]
end YangMills.Construction.ColdStepAtMirrorFrames
end
