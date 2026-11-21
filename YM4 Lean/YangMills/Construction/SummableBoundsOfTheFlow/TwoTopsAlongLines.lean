import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction
namespace DerivativeInterpolation
variable {F : BlockFrame}
def alongLine {k : ℕ} (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (s : ℝ)
    (V : F.GaugeField F.top) : F.GaugeField F.top :=
  leftTranslate (ColdStepAtMirrorFrames.bondSpread c X fun _ => s) V
structure IsControlledAlongLine (G : F.GaugeField F.top → ℝ) (V : F.GaugeField F.top) {k : ℕ}
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₃ : ℝ) : Prop where
  smooth : ∀ s : ℝ, |s| ≤ τ₀ → ContDiffThreeAlongBonds G (alongLine c X s V)
  thirdDeriv_le : ∀ s : ℝ, |s| ≤ τ₀ → ∀ e : Fin 3 → Fin k,
    |bondDeriv G (alongLine c X s V) (c ∘ e) (X ∘ e)| ≤ M₃
def DerivDiffLeOfCloseAlongLines : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (F F' : BlockFrame) (G : F.GaugeField F.top → ℝ) (G' : F'.GaugeField F'.top → ℝ)
    (V : F.GaugeField F.top) (V' : F'.GaugeField F'.top) (k : ℕ) (c : Fin k → F.Site F.top × Fin 4)
    (c' : Fin k → F'.Site F'.top × Fin 4) (X : Fin k → imaginaryQuaternions) (τ₀ M₀ M₃ : ℝ),
    1 ≤ k → k ≤ 2 → 0 < τ₀ → 0 < M₀ → 0 ≤ M₃ →
    (∀ ς : Fin k → ℝ, (∀ l, ς l = 1 ∨ ς l = -1) →
      IsControlledAlongLine G V c (fun l => ς l • X l) τ₀ M₃ ∧
      IsControlledAlongLine G' V' c' (fun l => ς l • X l) τ₀ M₃ ∧
      ∀ s : ℝ, |s| ≤ τ₀ → |G (alongLine c (fun l => ς l • X l) s V) -
        G' (alongLine c' (fun l => ς l • X l) s V')| ≤ M₀) →
    |bondDeriv G V c X - bondDeriv G' V' c' X| ≤
      C * (M₀ / τ₀ ^ k + M₀ ^ (1 - (k : ℝ) / 3) * M₃ ^ ((k : ℝ) / 3))
end DerivativeInterpolation
end YangMills.Construction
end
