import YangMills.Construction.RunningCouplingSlope.PlainSaddlesOnTheWholeLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower YangMills.Construction.Tower.FullSpace YangMills.Construction.PeriodicOperators
def MeanSaddleSymbolsInvertible : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : YangMills.Construction.InfiniteLattice.AmbientSpace,
      IsUnit (symbolHom (vectorIndices L k) (vectorIndices L k)
        (coeffZero (colourEdges L k 0) (vectorIndices L k) (vectorIndices L k)
          (FullLattice.edgeSaddleOfForm a L k)) (toComplexVec κ) :
        Module.End ℂ ((vectorIndices L k).UnitQuot → ℂ)) ∧
      IsUnit (symbolHom (ghostIndices L k) (ghostIndices L k)
        (coeffZero (colourEdges L k 0) (ghostIndices L k) (ghostIndices L k)
          (FullLattice.vertexSaddleOfForm L k)) (toComplexVec κ) :
        Module.End ℂ ((ghostIndices L k).UnitQuot → ℂ))
end YangMills.Construction.RunningCouplingSlope
end
