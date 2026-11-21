import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffPartialSumsTendsto : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ : ℝ) (O : Fin n → Set (Pt s .euclidean)),
    IsOpenTupleInBall ρ O →
    ∀ (F : testFns (boxSet O)) (χ : Fin n → Pt s .euclidean → ℝ),
      IsCutoffFor χ F →
      TestFnTendsto (boxSet O) (cutoffPartialSum (4 * ρ) χ F.1) F.1
end YangMills.Construction.AmbientPoints
