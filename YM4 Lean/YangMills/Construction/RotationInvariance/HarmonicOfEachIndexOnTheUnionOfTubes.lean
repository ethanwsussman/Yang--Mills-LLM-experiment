import YangMills.Construction.RotationInvariance.HarmonicsOnTheUnionOfTheTubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
abbrev indexHarmonic (S : ConnFamily) (φ₀ : openingAngles) {q : ℕ} (φ : Fin (q + 1) → realLabels)
    (h : ℤ) : (Fin (q + 1) → ℂ × ℂ) → ℂ :=
  tubeUnionHarmonic S φ₀ φ h
end EuclideanFunctionals
end YangMills.Construction
end
