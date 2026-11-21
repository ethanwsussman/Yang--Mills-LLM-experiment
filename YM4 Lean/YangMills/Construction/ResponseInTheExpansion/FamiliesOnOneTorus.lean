import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace WeightedResponses
variable {F : BlockFrame}
structure IsDecayingSiteFamily (L : ℕ) (σ δ e e₃ : ℝ) (g : F.Site F.depth → F.GaugeField F.depth → ℝ) : Prop where
  smooth : ∀ (y : F.Site F.depth) (U : F.GaugeField F.depth), IsSmallCurvature σ U → ContDiffThreeAlongBonds (g y) U
  gauge_invariant : ∀ (y : F.Site F.depth) (U : F.GaugeField F.depth) (γ : F.Site F.depth → UnitQuaternion),
    IsSmallCurvature σ U → g y (gaugeTransform γ U) = g y U
  decay : ∀ (y : F.Site F.depth) (U : F.GaugeField F.depth) (k : ℕ) (b : Fin k → F.Site F.depth × Fin 4)
    (X : Fin k → imaginaryQuaternions),
    IsSmallCurvature σ U → 1 ≤ k → k ≤ 3 → AreUnitVectors X →
    |bondDeriv (g y) U b X| ≤ (if k = 3 then e₃ else e) / torusDecayFactor L δ (bondSpan y b)
end WeightedResponses
end YangMills.Construction
end
