import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
def ContDiffBoundAlongTranslation : Prop :=
  ∀ (F : BlockFrame) (j k : ℕ) (c : Fin k → F.Site j × Fin 4) (X : Fin k → imaginaryQuaternions)
    (W : F.GaugeField j),
    (∀ i, F.period j i ≠ 0) → ∃ r₀ M : ℝ, 0 < r₀ ∧ 0 ≤ M ∧
      ∀ (r : ℝ) (G : F.GaugeField j → ℝ) (R : ℝ), r ≤ r₀ → 0 ≤ R →
      (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
        (∀ (q : ℕ) (c' : Fin q → F.Site j × Fin 4) (X' : Fin q → imaginaryQuaternions),
          ContDiffAt ℝ 3
            (fun u : Fin q → ℝ => G (leftTranslate (bondSpread c' X' u) (leftTranslate (bondSpread c X τ) W))) 0) ∧
        ∀ (q : ℕ) (c' : Fin q → F.Site j × Fin 4) (X' : Fin q → imaginaryQuaternions), q ≤ 3 →
          AreUnitVectors X' → |bondDeriv G (leftTranslate (bondSpread c X τ) W) c' X'| ≤ R) →
      ContDiffOn ℝ 3 (fun τ : Fin k → ℝ => G (leftTranslate (bondSpread c X τ) W)) (Metric.ball (0 : Fin k → ℝ) r) ∧
      ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (n : ℕ) (m : Fin n → Fin k), n ≤ 3 →
        |iteratedFDeriv ℝ n (fun τ' : Fin k → ℝ => G (leftTranslate (bondSpread c X τ') W)) τ
          fun i => Pi.single (m i) 1| ≤ M * R
end Estimates
end YangMills.Construction
end
