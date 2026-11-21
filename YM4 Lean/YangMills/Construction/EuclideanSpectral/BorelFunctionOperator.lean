import YangMills.Construction.EuclideanSpectral.ProjMeasureBoundedCalculus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanSpectral.ProjMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}
  [NeZero n]
def borelFnOp (E : ProjMeasure H n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ) : E.fnDomain u →ₗ[ℂ] H :=
  E.truncLimit u
end YangMills.Construction.EuclideanSpectral.ProjMeasure
