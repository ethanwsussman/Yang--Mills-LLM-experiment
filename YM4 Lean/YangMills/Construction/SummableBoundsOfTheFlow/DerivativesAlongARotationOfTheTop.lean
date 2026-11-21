import YangMills.Construction.ColdStepAtMirrorFrames.ExpansionOfAFamilyOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
def ContDiffBoundAlongRotationOfTop : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : BlockFrame) (V : F.GaugeField F.top)
    (c : Fin k → F.Site F.top × Fin 4) (X : Fin k → imaginaryQuaternions)
    (f : F.GaugeField F.top → ℝ) (r B : ℝ), AreUnitVectors X → 0 < r → k * r ≤ 1 → 0 ≤ B →
    (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r,
      ContDiffThreeAlongBonds f (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) →
    (∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ (j : ℕ) (c' : Fin j → F.Site F.top × Fin 4)
      (X' : Fin j → imaginaryQuaternions), j ≤ 3 → AreUnitVectors X' →
      |bondDeriv f (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V) c' X'| ≤ B) →
    ContDiffOn ℝ 3
        (fun τ : Fin k → ℝ => f (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V))
        (Metric.ball 0 r) ∧
      ∀ τ ∈ Metric.ball (0 : Fin k → ℝ) r, ∀ j : ℕ, j ≤ 3 →
        ‖iteratedFDeriv ℝ j
            (fun τ : Fin k → ℝ => f (leftTranslate (ColdStepAtMirrorFrames.bondSpread c X τ) V)) τ‖ ≤
          C * B
end Estimates
end YangMills.Construction
end
