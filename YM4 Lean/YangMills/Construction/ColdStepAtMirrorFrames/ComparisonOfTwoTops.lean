import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import YangMills.Construction.ColdStepAtMirrorFrames.MirrorTorusAndFrames
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
def DerivativesCloseOfValuesClose : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ)
    (G' : F'.GaugeField F'.top → ℝ) (s₁ s₂ τ₀ M₀ B : ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (Y : F.Cell) (Y' : F'.Cell) (r : ℕ),
    (∀ i, 2 ≤ F.extent i) → (∀ i, 2 ≤ F'.extent i) → 0 < τ₀ → τ₀ ≤ 1 → s₁ + 8 * τ₀ ≤ s₂ →
    0 < M₀ → M₀ ≤ B →
    (∀ W : F.GaugeField F.top, IsSmallCurvature s₂ W → IsBondAnalyticAt G W ∧
      ∀ (e : Fin 6 → F.Site F.top × Fin 4) (X : Fin 6 → imaginaryQuaternions),
        AreUnitVectors X → |bondDeriv G W e X| ≤ B) →
    (∀ W : F'.GaugeField F'.top, IsSmallCurvature s₂ W → IsBondAnalyticAt G' W ∧
      ∀ (e : Fin 6 → F'.Site F'.top × Fin 4) (X : Fin 6 → imaginaryQuaternions),
        AreUnitVectors X → |bondDeriv G' W e X| ≤ B) →
    (∀ (W : F.GaugeField F.top) (W' : F'.GaugeField F'.top), IsSmallCurvature s₂ W →
      IsSmallCurvature s₂ W' →
      AgreeOnBall (finiteCells F) W (finiteCells F') W' Y Y' r → |G W - G' W'| ≤ M₀) →
    IsSmallCurvature s₁ V → IsSmallCurvature s₁ V' →
    AgreeOnBall (finiteCells F) V (finiteCells F') V' Y Y' r →
    ∀ (k : ℕ) (h : Fin k → (Fin 4 → ℤ) × Fin 4) (X : Fin k → imaginaryQuaternions), k ≤ 2 →
      (∀ l, BondWithinRadius r (h l)) → AreUnitVectors X →
      |bondDeriv G V (bondsAt Y h) X - bondDeriv G' V' (bondsAt Y' h) X| ≤
        C * (M₀ / τ₀ ^ 2 + M₀ ^ (2 / 3 : ℝ) * B ^ (1 / 3 : ℝ))
end YangMills.Construction.ColdStepAtMirrorFrames
end
