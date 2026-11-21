import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import YangMills.Construction.ColdStepAtMirrorFrames.FamiliesOnFramesAndTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.TorusFields
namespace YangMills.Construction.Estimates
def TopFamilyDerivBoundsOnTori : Prop :=
  ∀ (L t n₀ K : ℕ) (s : ℝ) (g : TopLevelFamily) (e : ℕ → ℕ → ℝ),
    (∀ F, IsCubicTopTorus L t n₀ F → ∀ (Y : F.Cell) (V : F.GaugeField F.top) (k : ℕ)
      (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions),
      IsSmallCurvature s V → 1 ≤ k → k ≤ K → AreUnitVectors X →
      |bondDeriv (g F Y) V c X| ≤ e k (bondSpan Y c)) →
    ∀ n [NeZero n], n₀ ≤ n → ∀ (y : TorusSite n) (V : TorusField n), IsCold s V →
      ∀ (k : ℕ) (c : Fin k → TorusBond n) (X : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ K →
        AreUnitVectors X →
        |mixedDeriv (densityOfTopFamily L t g n y) V c X| ≤ e k (supportDiam y c)
end YangMills.Construction.Estimates
end
