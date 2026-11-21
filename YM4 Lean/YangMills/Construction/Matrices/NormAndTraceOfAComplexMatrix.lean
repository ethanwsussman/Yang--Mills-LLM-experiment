import YangMills.Construction.Conventions.OneLoopLawDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.RectangularMatrix
def opNormValue {m k : ℕ} [NeZero m] [NeZero k] (X : Matrix (Fin m) (Fin k) ℂ) : ℝ :=
  OneLoopNotation.opNormOf (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X))
def diagSum {m : ℕ} [NeZero m] (X : Matrix (Fin m) (Fin m) ℂ) : ℂ := ∑ i, X i i
end YangMills.Construction.Matrices.RectangularMatrix
