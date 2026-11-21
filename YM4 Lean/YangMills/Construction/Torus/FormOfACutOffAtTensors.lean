import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffSeriesAtTensors : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ C : ℝ) (U : Fin n → Set (Pt s .euclidean))
    (Φ : (Fin n → Pt s .euclidean → ℂ) → ℂ) (χ : Fin n → Pt s .euclidean → ℝ),
    IsOpenTupleInBall ρ U → 0 ≤ C → IsComplexMultilinearOnComponents U Φ →
    IsComplexGradNormBounded U C Φ → IsCutoff U χ →
    ∀ f : Fin n → Pt s .euclidean → ℂ,
      (∀ i, ofSinglePoint (f i) ∈ testFns (Torus.FourierBox.fundamentalBoxPow s 1 (4 * ρ))) →
      cutoffSeries (4 * ρ) Φ χ (tensorProd f) = Φ fun i x => (χ i x : ℂ) * f i x
end YangMills.Construction.AmbientPoints
