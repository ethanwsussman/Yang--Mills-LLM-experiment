import YangMills.Construction.RotationInvariance.OneFunctionOnAllTubes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RealPlane
namespace EuclideanFunctionals
abbrev tubeUnionFunction (S : ConnFamily) {q : ℕ} (φ : Fin (q + 1) → realLabels) :
    (Fin (q + 1) → ℂ × ℂ) → ℂ :=
  unionKernel S φ
end EuclideanFunctionals
end YangMills.Construction
end
