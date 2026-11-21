import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints
def CutoffsEqualOneOnProjections : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ : ℝ) (O : Fin n → Set (Pt s .euclidean)),
    IsOpenTupleInBall ρ O →
      (∀ K : Set (Tuple s .euclidean n), IsCompact K → K ⊆ boxSet O →
        ∃ χ, IsCutoff O χ ∧ ∀ i, ∀ y ∈ factorProjection i K, χ i y = 1) ∧
      ∀ (F : testFns (boxSet O)) (χ : Fin n → Pt s .euclidean → ℝ),
        IsCutoff O χ → CutOffIsOneOnProjections F.1 χ → IsCutoffFor χ F
end YangMills.Construction.AmbientPoints
