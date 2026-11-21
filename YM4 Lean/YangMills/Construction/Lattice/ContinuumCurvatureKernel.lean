import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open TorusMetric
def unitDirection (u : Fin 4 → ℝ) : Fin 4 → ℝ := fun μ => u μ / euclidNormVec u
def householderMatrix (u : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  1 - (2 : ℝ) • Matrix.vecMulVec (unitDirection u) (unitDirection u)
theorem householderMatrix_apply (u : Fin 4 → ℝ) (μ ν : Fin 4) :
    householderMatrix u μ ν = (if μ = ν then 1 else 0) - 2 * u μ * u ν / euclidNormVec u ^ 2 := by
  simp only [householderMatrix, unitDirection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Matrix.one_apply, smul_eq_mul]
  ring
@[ext]
structure AxisPlane where
  lower : Fin 4
  upper : Fin 4
  lower_lt_upper : lower < upper
def continuumCurvatureKernel (P P' : AxisPlane) (u : Fin 4 → ℝ) : ℝ :=
  (householderMatrix u P.lower P'.lower * householderMatrix u P.upper P'.upper -
      householderMatrix u P.lower P'.upper * householderMatrix u P.upper P'.lower) /
    (Real.pi ^ 2 * euclidNormVec u ^ 4)
def naturalEntryScale {L m K : ℕ} (p q : PlaquetteAtLevel L m K 0) : ℝ :=
  meshSize L (K : ℤ) ^ 4 /
    (Real.pi ^ 2 * torusEuclidNorm (p.barycenter - q.barycenter) ^ 4)
end YangMills.Construction.PeriodicLattice
