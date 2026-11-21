import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace LocalComparison
def DerivDiffLeOfValueDiffLe : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (σ κ A h CE : ℝ) (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ)
    (G' : F'.GaugeField F'.top → ℝ) (Y : F.Cell) (Y' : F'.Cell) (V : F.GaugeField F.top)
    (V' : F'.GaugeField F'.top) (q k : ℕ) (b : Fin k → (Fin 4 → ℤ) × Fin 4)
    (X : Fin k → imaginaryQuaternions), 0 < σ → 0 < κ → 1 ≤ A → 0 < h → k ≤ 2 →
    C₀ * (A * (1 + 64 / σ + (64 / σ) ^ 2 + 1)) + A ≤ CE →
    (∀ W : F.GaugeField F.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G W) →
    (∀ W : F'.GaugeField F'.top, IsSmallCurvature (5 / 4 * σ) W → ContDiffThreeAlongBonds G' W) →
    (∀ (W : F.GaugeField F.top) (c : Fin 3 → F.Site F.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G W c X'| ≤ A * h) →
    (∀ (W : F'.GaugeField F'.top) (c : Fin 3 → F'.Site F'.top × Fin 4) (X' : Fin 3 → imaginaryQuaternions),
      IsSmallCurvature (5 / 4 * σ) W → AreUnitVectors X' → |bondDeriv G' W c X'| ≤ A * h) →
    (∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature (5 / 4 * σ) W →
      IsSmallCurvature (5 / 4 * σ) W' → AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' q →
      |G W - G' W'| ≤ A * h * Real.exp (-(κ * q / 2 ^ 7))) →
    IsSmallCurvature (9 / 8 * σ) V → IsSmallCurvature (9 / 8 * σ) V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' q → (∀ l, BondWithinRadius q (b l)) →
    AreUnitVectors X →
    |bondDeriv G V (bondsAt Y b) X - bondDeriv G' V' (bondsAt Y' b) X| ≤
      CE * h * Real.exp (-(2 * (κ / 2 ^ 10) * q))
end LocalComparison
end YangMills.Construction
end
