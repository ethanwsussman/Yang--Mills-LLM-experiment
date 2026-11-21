import YangMills.Construction.LawByMomentsOfTheFlow.WindowOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def colourFormIdentitiesStatement : Prop :=
  (∀ (m : ℕ) (F : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions) (p : TorusFields.TorusPlaquette m),
    curlNorm (toColourForm F) p = ‖ResponseInTheExpansion.lieFormCurl F p‖) ∧
  (∀ (L : ℕ) [NeZero L] (n : ℕ) [NeZero n] (a ρA : ℝ) (u : ℕ)
      (A : TorusFields.TorusBond n → BlockAverages.imaginaryQuaternions),
    pushColours a ρA L u (toColourForm A) = toColourForm (ResponseInTheExpansion.responseOfLieForm a ρA L u A)) ∧
  (∀ (m : ℕ) (F G : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions),
    (fun e b => toColourForm F e b + toColourForm G e b) = toColourForm fun b => F b + G b) ∧
  ∀ (m : ℕ) (F G : TorusFields.TorusBond m → BlockAverages.imaginaryQuaternions),
    (fun e b => toColourForm F e b - toColourForm G e b) = toColourForm fun b => F b - G b
end YangMills.Construction.MomentLaw
end
