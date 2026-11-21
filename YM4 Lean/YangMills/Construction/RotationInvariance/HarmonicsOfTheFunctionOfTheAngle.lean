import YangMills.Construction.RotationInvariance.EntireFunctionOfTheAngleOnAPencil
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Complex (I)
open RealPlane
namespace EuclideanFunctionals
def angleHarmonic (S : ConnFamily) (θ₀ : openingAngles) {q : ℕ}
    (y : Fin (q + 1) → RealPlane) (φ : Fin (q + 1) → realLabels) (ν : ℤ) : ℂ :=
  ((2 / Real.pi : ℝ) : ℂ) *
    ∫ t : ℝ in (0 : ℝ)..(Real.pi / 2),
      angleFunction S θ₀ y φ (t : ℂ) * Complex.exp (-(4 * I * (ν : ℂ) * (t : ℂ)))
end EuclideanFunctionals
end YangMills.Construction
end
