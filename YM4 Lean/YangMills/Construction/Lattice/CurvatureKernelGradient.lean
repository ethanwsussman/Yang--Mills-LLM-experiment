import YangMills.Construction.Lattice.ContinuumCurvatureKernel
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.TorusMetric
open scoped ENNReal
def axisPlaneEquivOrderedPairs : AxisPlane ≃ {p : Fin 4 × Fin 4 // p.1 < p.2} where
  toFun P := ⟨(P.lower, P.upper), P.lower_lt_upper⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance instFintypeAxisPlane : Fintype AxisPlane :=
  Fintype.ofEquiv _ axisPlaneEquivOrderedPairs.symm
def gradientVec (f : (Fin 4 → ℝ) → ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun α => fderiv ℝ f v (Pi.single α 1)
def curvatureKernelGradientSup : ℝ≥0∞ :=
  ⨆ (P : AxisPlane) (Q : AxisPlane) (u : Fin 4 → ℝ) (_ : euclidNormVec u = 1),
    ENNReal.ofReal (euclidNormVec (gradientVec (continuumCurvatureKernel P Q) u))
end YangMills.Construction.PeriodicLattice
