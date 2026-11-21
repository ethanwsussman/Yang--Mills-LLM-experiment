import YangMills.Construction.ColdStepAtMirrorFrames.NumbersOfTheColdChainFormForm
import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def GapTermsChartBounds : Prop :=
  ∀ L : ℕ, Odd L → ∃ Cg : ℝ, 0 < Cg ∧ ∀ (F : BlockFrame) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (A : ℝ), F.blockSide = L → (∀ i, 0 < F.extent i) → 2 ≤ A →
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
    (∀ (c : F.Site F.top × Fin 4) (h : Fin 4 → ℤ) (π : Equiv.Perm (Fin 4)), h ∈ centredCube L →
      ‖contourHolonomyDefect (chartedField w V) V c h π - 1‖ ≤ 1 / 2) →
    ContDiffAt ℝ 3 (readInChart (gapExcessSum A) w V) 0 ∧
    ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |fderiv ℝ (readInChart (gapExcessSum A) w V) 0 (bondVariation b e)| ≤ Cg * ‖e‖ ∧
      |fderiv ℝ (fun ζ => fderiv ℝ (readInChart (gapExcessSum A) w V) ζ (bondVariation b e)) 0
          (bondVariation b' e')| ≤
        (if siteSupDist b.1.1 b'.1.1 ≤ 10 * L then Cg else 0) * ‖e‖ * ‖e'‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
