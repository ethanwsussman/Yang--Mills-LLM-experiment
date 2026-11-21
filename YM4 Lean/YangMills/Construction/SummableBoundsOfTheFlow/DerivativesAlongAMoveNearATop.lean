import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
def ContDiffBoundOnParameterBall : Prop :=
  ∀ (F : BlockFrame) (j k : ℕ) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions),
    ∃ r₀ C : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ (V : F.GaugeField j) (G : F.GaugeField j → ℝ) (D : ℝ), 0 ≤ D →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (q : ℕ) (c' : Fin q → F.Site j × Fin 4)
        (X' : Fin q → imaginaryQuaternions),
        AreUnitVectors X' → ContDiffAt ℝ 3
          (fun σ : Fin q → ℝ => G (leftTranslate (bondSpread c' X' σ) (leftTranslate (bondSpread c X τ) V))) 0) →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (i : ℕ) (c' : Fin i → F.Site j × Fin 4)
        (X' : Fin i → imaginaryQuaternions),
        i ≤ 3 → AreUnitVectors X' → |bondDeriv G (leftTranslate (bondSpread c X τ) V) c' X'| ≤ D) →
      ContDiffOn ℝ 3 (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) (Metric.ball 0 r) ∧
      ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ i, i ≤ 3 →
        ‖iteratedFDeriv ℝ i (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) V)) τ‖ ≤ C * D
end Estimates
end YangMills.Construction
end
