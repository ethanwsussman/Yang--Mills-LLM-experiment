import YangMills.Construction.ColdStepAtMirrorFrames.PullbackThroughTheChartForm
import YangMills.Construction.SummableBoundsOfTheFlow.FamiliesOfANorm
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages YangMills.Construction.FamilyNorms
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CentredFamilyInChartBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L t n₀ : ℕ) (σ δ ε ε₃ : ℝ) (f : LocalFamily), 0 ≤ δ → 0 ≤ ε →
    IsNormBoundedLocalFamily L t n₀ σ δ ε ε₃ f →
    ∀ (F : BlockFrame) (w : F.Site F.depth → Fin 4 → imaginaryQuaternions) (V : F.GaugeField F.top) (y : F.Site F.depth), IsCubicTorusAbove L t n₀ F →
      IsSmallCurvature σ (chartedField w V) → (∀ b ∈ chordBonds (finiteCells F), ‖w b.1 b.2‖ ≤ 1) →
      ContDiffAt ℝ 3 (readInChart (subtractTrivial f F y) w V) 0 ∧
      (∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |fderiv ℝ (readInChart (subtractTrivial f F y) w V) 0 (bondVariation b e)| ≤
          C * ε * ‖e‖ / torusDecayFactor L δ (siteSupDist y b.1.1)) ∧
      ∀ (b : ↥(chordBonds (finiteCells F))) (e : BondVector),
        |secondDerivAlong (readInChart (subtractTrivial f F y) w V) 0 (bondVariation b e) (bondVariation b e)| ≤ C * ε * ‖e‖ ^ 2
end YangMills.Construction.ColdStepAtMirrorFrames
end
