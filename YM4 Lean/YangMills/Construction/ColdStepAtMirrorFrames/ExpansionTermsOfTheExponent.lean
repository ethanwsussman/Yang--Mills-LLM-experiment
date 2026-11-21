import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def ExpansionTermsChartBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame) (V : F.GaugeField F.top)
    (w : F.Site F.depth → Fin 4 → imaginaryQuaternions), 0 ≤ δ → 0 ≤ E → HasDecayingDerivs L t n₀ σ δ E E₃ f →
    IsCubicTorusAbove L t n₀ F →
    (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) → IsSmallCurvature σ (chartedField w V) →
    ContDiffAt ℝ 3 (readInChart (centredExpansionSum f) w V) 0 ∧
    ∀ (b b' : ↥(chordBonds (finiteCells F))) (e e' : BondVector),
      |fderiv ℝ (readInChart (centredExpansionSum f) w V) 0 (bondVariation b e)| ≤
        C * E * (∑ y ∈ sitesOfCells (finiteCells F) F.depth, Real.exp (-(δ * (siteSupDist y b.1.1 : ℝ)))) * ‖e‖ ∧
      |fderiv ℝ (fun ζ => fderiv ℝ (readInChart (centredExpansionSum f) w V) ζ (bondVariation b e)) 0
          (bondVariation b' e')| ≤
        C * E * expansionDecayKernel F δ b b' * ‖e‖ * ‖e'‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
