import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
def BoundedComplexFormDistribution : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ C : ℝ) (O : Fin n → Set (Pt s .euclidean))
    (B : (Fin n → Pt s .euclidean → ℂ) → ℂ),
    IsOpenTupleInBall ρ O → 0 ≤ C → IsComplexMultilinearOnComponents O B →
    IsComplexGradNormBounded O C B →
    ∃ T : testFns (boxSet O) → ℂ,
      HasOrderLE (5 * n + 1) T ∧ AgreesWithFormOnRealTensors B T ∧
      (∀ (F : testFns (boxSet O)) (χ : Fin n → Pt s .euclidean → ℝ),
        IsCutoffFor χ F →
          T F = cutoffSeries (4 * ρ) B χ F.1 ∧
          ENNReal.ofReal ‖T F‖ ≤
            ENNReal.ofReal (C * bumpNumber n ρ) *
              (∏ i, c1GradNorm fun x => (χ i x : ℂ)) * cnNorm (5 * n + 1) F.1) ∧
      ∀ T' : testFns (boxSet O) → ℂ,
        IsDistrib T' → AgreesWithFormOnRealTensors B T' → T' = T
end YangMills.Construction.AmbientPoints
