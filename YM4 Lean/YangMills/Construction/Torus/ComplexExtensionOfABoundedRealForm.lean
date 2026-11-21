import YangMills.Construction.Torus.MultilinearFormsOnCompactlySupportedComponents
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AmbientPoints.ComplexExtension
def ExistsComplexExtension : Prop :=
  ∀ (s : Conventions.StandingParameters) (n : ℕ) (ρ c : ℝ) (O : Fin n → Set (Pt s .euclidean))
    (B : EntryTuple O → ℝ),
    IsOpenTupleInBall ρ O → 0 ≤ c → IsMultilinearOnComponents B → IsGradNormBounded c B →
    ∃ Bc : (Fin n → Pt s .euclidean → ℂ) → ℂ,
      IsComplexMultilinearOnComponents O Bc ∧ IsComplexGradNormBounded O (2 ^ n * c) Bc ∧
      ∀ g : EntryTuple O, Bc (fun i x => ((g i).1 x : ℂ)) = (B g : ℂ)
end YangMills.Construction.AmbientPoints.ComplexExtension
