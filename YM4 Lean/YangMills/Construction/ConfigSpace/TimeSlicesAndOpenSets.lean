import YangMills.Construction.Continuum.DiagonalFlatSchwartz
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigSpace
variable {n : ℕ}
def lastCoord (u : Fin 4 → ℝ) : ℝ := u 3
def argTime (x : Config n) (i : Fin n) : ℝ := lastCoord (x i)
def distinctArgs (n : ℕ) : Set (Config n) := TestFunctions.injectiveTuples (Fin 4 → ℝ) n
def posTimeSet (n : ℕ) : Set (Config n) :=
  {x | x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧ ∀ i, argTime x i > 0}
def negTimeSet (n : ℕ) : Set (Config n) :=
  {x | x ∈ TestFunctions.injectiveTuples (Fin 4 → ℝ) n ∧ ∀ i, -argTime x i > 0}
def upperHalfSpace : Set (Fin 4 → ℝ) := {u | lastCoord u > 0}
def zeroTimeHyperplane : Set (Fin 4 → ℝ) := {v | lastCoord v = 0}
theorem euclidNorm_sq_eq_sum_sq (x : Config n) :
    euclidNorm x ^ 2 = ∑ i, TorusMetric.euclidNormVec (x i) ^ 2 := by
  unfold euclidNorm TorusMetric.euclidNormVec
  rw [Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => (Real.sq_sqrt (by positivity)).symm
theorem isOpen_upperHalfSpace : IsOpen upperHalfSpace :=
  isOpen_lt continuous_const (continuous_apply (3 : Fin 4))
end YangMills.Construction.ConfigSpace
end
