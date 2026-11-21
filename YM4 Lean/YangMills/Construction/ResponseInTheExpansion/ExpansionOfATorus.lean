import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LinearResponse
open BlockAverages ColdStepAtMirrorFrames
structure IsRegularOnTorus (L t n₀ : ℕ) (σ δ E E₃ : ℝ) (f : LocalFamily) (F : BlockFrame) : Prop where
  smooth : IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth),
    IsSmallCurvature σ W → ContDiffThreeAlongBonds (f F y) W
  gauge_invariant : IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth)
    (γ : F.Site F.depth → UnitQuaternion), IsSmallCurvature σ W → f F y (gaugeTransform γ W) = f F y W
  decay : IsCubicTorusAbove L t n₀ F → ∀ (y : F.Site F.depth) (W : F.GaugeField F.depth) (k : ℕ)
    (c : Fin k → F.Site F.depth × Fin 4) (X : Fin k → imaginaryQuaternions), IsSmallCurvature σ W → 1 ≤ k → k ≤ 3 →
    AreUnitVectors X →
    |bondDeriv (f F y) W c X| ≤ (if k = 3 then E₃ else E) / torusDecayFactor L δ (bondSpan y c)
  locality : IsCubicTorusAbove L t n₀ F →
    ∀ (y : F.Site F.depth) (W W' : F.GaugeField F.depth) (r k : ℕ)
      (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    IsSmallCurvature σ W → IsSmallCurvature σ W' → AgreeOnBox W W' y y r → k ≤ 2 →
    (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
    |bondDeriv (subtractTrivial f F y) W (bondsAt y h) X - bondDeriv (subtractTrivial f F y) W' (bondsAt y h) X| ≤
      E / torusDecayFactor L δ r
end YangMills.Construction.LinearResponse
end
