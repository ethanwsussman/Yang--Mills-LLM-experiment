import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages
namespace ColdStepAtMirrorFrames
def HaarExcessSumDiagonalBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions),
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
    ContDiffAt ℝ 3 (haarExcessSum w) 0 ∧
    ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |fderiv ℝ (haarExcessSum w) 0 (bondVariation b e)| ≤ C * ‖e‖ ∧
      |fderiv ℝ (fun ζ => fderiv ℝ (haarExcessSum w) ζ (bondVariation b e)) 0 (bondVariation b' e')| ≤
        (if b = b' then C else 0) * ‖e‖ * ‖e'‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
