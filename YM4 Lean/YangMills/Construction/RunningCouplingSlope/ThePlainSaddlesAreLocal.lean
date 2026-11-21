import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Tower.FullSpace PeriodicOperators
open PeriodicOperators.LogDetSecondDerivs (IsRealOnRealFields)
def SaddleKernelsAreLocal : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    IsLocalOpFun (colourEdges L k 0) (vectorIndices L k) (vectorIndices L k)
      (FullLattice.edgeSaddleOfForm a L k) ∧
    IsLocalOpFun (colourEdges L k 0) (ghostIndices L k) (ghostIndices L k)
      (FullLattice.vertexSaddleOfForm L k) ∧
    IsRealOnRealFields (colourEdges L k 0) (vectorIndices L k)
      (FullLattice.edgeSaddleOfForm a L k) ∧
    IsRealOnRealFields (colourEdges L k 0) (ghostIndices L k) (FullLattice.vertexSaddleOfForm L k)
end YangMills.Construction.RunningCouplingSlope
end
