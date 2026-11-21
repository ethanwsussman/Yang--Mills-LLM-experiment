import YangMills.Construction.LinearAlgebra.BivectorsReflectionsAngles
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Exterior
def freeCurvaturePropagator (x : Fin 4 → ℝ) : Bivector →ₗ[ℝ] Bivector :=
  (1 / (Real.pi ^ 2 * TorusMetric.euclidNormVec x ^ 4)) •
    exteriorSq (householder ((TorusMetric.euclidNormVec x)⁻¹ • x))
end YangMills.Construction.Exterior
