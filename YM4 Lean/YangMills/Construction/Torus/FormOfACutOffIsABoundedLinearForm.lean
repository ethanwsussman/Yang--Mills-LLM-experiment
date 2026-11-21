import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffSeriesBoundedLinear : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ C : ℝ) (U : Fin n → Set (Pt s .euclidean))
    (Φ : (Fin n → Pt s .euclidean → ℂ) → ℂ) (χ : Fin n → Pt s .euclidean → ℝ),
    IsOpenTupleInBall ρ U → 0 ≤ C → IsComplexGradNormBounded U C Φ → IsCutoff U χ →
      (∀ F ∈ testFns (Torus.FourierBox.fundamentalBoxPow s n (4 * ρ)),
        Summable (fun k : Fin (4 * n) → ℤ =>
          Torus.FourierBox.fourierCoeff (4 * ρ) F k * Φ (cutoffModeTuple (4 * ρ) χ k)) ∧
        ENNReal.ofReal ‖cutoffSeries (4 * ρ) Φ χ F‖ ≤
          ENNReal.ofReal (C * bumpNumber n ρ) *
            (∏ i, c1GradNorm fun x => (χ i x : ℂ)) * cnNorm (5 * n + 1) F) ∧
      IsComplexLinearForm fun F : testFns (Torus.FourierBox.fundamentalBoxPow s n (4 * ρ)) =>
        cutoffSeries (4 * ρ) Φ χ F.1
end YangMills.Construction.AmbientPoints
