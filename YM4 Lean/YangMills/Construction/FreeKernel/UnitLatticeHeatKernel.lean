import YangMills.Construction.FreeKernel.OneDimensionalLatticeKernels
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.UnitLattice
def integerHeatKernel (T : ℝ) (m : ℤ) : ℝ := (YangMills.Construction.LatticeKernel.discreteHeatKernel T m).re
def forwardDiff (f : ℤ → ℝ) : ℤ → ℝ := fun m => f (m + 1) - f m
def backwardDiff (f : ℤ → ℝ) : ℤ → ℝ := fun m => f (m - 1) - f m
variable {d : ℕ}
def l1Length (m : Fin d → ℤ) : ℝ := ∑ i, |(m i : ℝ)|
def latticeForwardDiff (i : Fin d) (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  fun m => f (m + Pi.single i 1) - f m
def latticeBackwardDiff (i : Fin d) (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  fun m => f (m - Pi.single i 1) - f m
def wordDiff (w : List (Fin d ⊕ Fin d)) (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  w.foldr (fun o g => Sum.elim (fun i => latticeForwardDiff i g) (fun i => latticeBackwardDiff i g) o) f
def latticeLaplacian (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  fun m => ∑ i, (2 * f m - f (m + Pi.single i 1) - f (m - Pi.single i 1))
def latticeHeatKernel (T : ℝ) (m : Fin d → ℤ) : ℝ := ∏ i, integerHeatKernel T (m i)
end YangMills.Construction.FreeKernel.UnitLattice
end
