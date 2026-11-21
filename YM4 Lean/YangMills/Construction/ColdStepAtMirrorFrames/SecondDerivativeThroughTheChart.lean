import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def ChartSecondDerivBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F : BlockFrame) (U : F.GaugeField F.top) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : F.GaugeField F.depth → E),
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
    ContDiffThreeAlongBonds G (chartedField w U) →
    ContDiffAt ℝ 3 (readInChart G w U) 0 ∧
    (∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      ∃ X X' Q : imaginaryQuaternions, ‖X‖ ≤ C * ‖e‖ ∧ ‖X'‖ ≤ C * ‖e'‖ ∧ ‖Q‖ ≤ C * ‖e‖ * ‖e'‖ ∧
        fderiv ℝ (readInChart G w U) 0 (bondVariation b e) = bondDeriv G (chartedField w U) ![b.1] ![X] ∧
        fderiv ℝ (fun ζ => fderiv ℝ (readInChart G w U) ζ (bondVariation b e)) 0 (bondVariation b' e') =
          bondDeriv G (chartedField w U) ![b'.1, b.1] ![X', X] +
            if b = b' then bondDeriv G (chartedField w U) ![b.1] ![Q] else 0) ∧
    ∀ (B₁ : ↥(chordBonds (finiteCells F)) → ℝ)
      (B₂ : ↥(chordBonds (finiteCells F)) → ↥(chordBonds (finiteCells F)) → ℝ),
      (∀ (b : ↥(chordBonds (finiteCells F))) (X : imaginaryQuaternions), ‖X‖ = 1 →
        ‖bondDeriv G (chartedField w U) ![b.1] ![X]‖ ≤ B₁ b) →
      (∀ (b b' : ↥(chordBonds (finiteCells F))) (X X' : imaginaryQuaternions), ‖X‖ = 1 → ‖X'‖ = 1 →
        ‖bondDeriv G (chartedField w U) ![b'.1, b.1] ![X', X]‖ ≤ B₂ b' b) →
      ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
        ‖fderiv ℝ (readInChart G w U) 0 (bondVariation b e)‖ ≤ C * B₁ b * ‖e‖ ∧
        ‖fderiv ℝ (fun ζ => fderiv ℝ (readInChart G w U) ζ (bondVariation b e)) 0 (bondVariation b' e')‖ ≤
          (C ^ 2 * B₂ b' b + if b = b' then C * B₁ b else 0) * ‖e‖ * ‖e'‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
