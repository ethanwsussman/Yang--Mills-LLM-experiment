import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffSeriesIndepOfCutoff : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ C : ℝ) (U : Fin n → Set (Pt s .euclidean))
    (Φ : (Fin n → Pt s .euclidean → ℂ) → ℂ),
    IsOpenTupleInBall ρ U → 0 ≤ C → IsComplexMultilinearOnComponents U Φ →
    IsComplexGradNormBounded U C Φ →
    ∀ (F : testFns (boxSet U)) (χ χ' : Fin n → Pt s .euclidean → ℝ),
      IsCutoffFor χ F → IsCutoffFor χ' F →
      cutoffSeries (4 * ρ) Φ χ F.1 = cutoffSeries (4 * ρ) Φ χ' F.1
end YangMills.Construction.AmbientPoints
