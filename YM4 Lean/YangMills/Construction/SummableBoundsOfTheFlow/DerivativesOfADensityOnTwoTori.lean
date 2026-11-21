import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace DerivativeInterpolation
def interpolatedSize (σ M₀ M₃ : ℝ) (k : ℕ) : ℝ :=
  M₀ / (σ / 64) ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3)
def DensityDerivDiffLeOnTwoTori : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L t n₀ : ℕ) (σ M₀ M₃ : ℝ) (g : TopLevelFamily) (F F' : BlockFrame) (Y : F.Cell)
    (Y' : F'.Cell) (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (r k : ℕ)
    (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions),
    0 < σ → 0 < M₀ → 0 ≤ M₃ → 1 ≤ k → k ≤ 2 → IsCubicTopTorus L t n₀ F → IsCubicTopTorus L t n₀ F' →
    IsLocalDensity L t n₀ (5 / 4 * σ) g →
    (∀ (F'' : BlockFrame) (Y'' : F''.Cell) (W : F''.GaugeField F''.top) (c : Fin 3 → F''.Site F''.top × Fin 4)
      (X' : Fin 3 → imaginaryQuaternions), IsCubicTopTorus L t n₀ F'' → IsSmallCurvature (5 / 4 * σ) W →
      AreUnitVectors X' → |bondDeriv (g F'' Y'') W c X'| ≤ M₃) →
    (∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * σ) W →
      IsSmallCurvature (5 / 4 * σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r →
      |g F Y W - g F' Y' W'| ≤ M₀) →
    IsSmallCurvature (9 / 8 * σ) V → IsSmallCurvature (9 / 8 * σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r → (∀ l, BondWithinRadius r (h l)) →
    AreUnitVectors X →
    |bondDeriv (g F Y) V (bondsAt Y h) X - bondDeriv (g F' Y') V' (bondsAt Y' h) X| ≤
      C * interpolatedSize σ M₀ M₃ k
end DerivativeInterpolation
end YangMills.Construction
end
