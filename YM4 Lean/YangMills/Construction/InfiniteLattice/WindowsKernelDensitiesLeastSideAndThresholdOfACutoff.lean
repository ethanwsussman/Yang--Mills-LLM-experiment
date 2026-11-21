import YangMills.Construction.InfiniteLattice.WindowsKernelOperatorAndDensitiesAtOneSpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.CutoffLattice
open YangMills.Construction.InfiniteLattice
abbrev WindowAt (L K : ℕ) : Type := LinkWindow (spacingAt L K)
variable {L K : ℕ}
namespace WindowAt
theorem haarProd_univ (W : WindowAt L K) : W.haarProd Set.univ = 1 := by
  unfold LinkWindow.haarProd YangMills.Construction.Matrices.ComplexMatrix2.haarPi
  exact measure_univ
section Kernel
variable (hL : YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L)
  (W : WindowAt L K) (β : ℝ)
def plaquetteActionSum (V : W.Assignments) (U : FieldsAt L K) : ℝ :=
  ∑ᶠ p ∈ W.faces,
    (1 / 2) * (YangMills.Construction.Matrices.ComplexMatrix2.fullTrace
      (faceHolonomy (W.glue (spacingAt_pos hL K) V U) p :
        YangMills.Construction.Matrices.ComplexMatrix2)).re
def localEnergy (V : W.Assignments) (ξ : LinkVariables W.rim) : ℝ :=
  W.plaquetteActionSum hL V (W.fieldOfRimValues (spacingAt_pos hL K) ξ)
def boltzmannKernel (V : W.Assignments) (ξ : LinkVariables W.rim) : ℝ :=
  Real.exp (β * W.localEnergy hL V ξ) / ∫ V', Real.exp (β * W.localEnergy hL V' ξ) ∂W.haarProd
end Kernel
end WindowAt
end YangMills.Construction.CutoffLattice
