import YangMills.Construction.Towers.OperatorsDependingLocallyOnAField
import YangMills.Construction.Towers.TheSecondDerivativesOfTheDensity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.AbelianFieldDensity
def SecondDerivViaLogTraces.Statement : Prop :=
  ∀ z : ℝ, 0 < z → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (x : Tower.FullSpace.Vertex L 0 0) (e e' : Tower.FullSpace.PositiveEdge (Tower.meshAt L 0 0)),
      Tower.AbelianFieldDensity.secondDerivative z x e e' =
        Tower.LocalFamilies.logTraceHessian (Tower.UnitLatticeL2.vertexPos L)
            (Tower.AbelianFieldDensity.laplacianOp (L := L)) z
            (x : InfiniteLattice.AmbientSpace) e e' -
          (1 / 2 : ℂ) * Tower.LocalFamilies.logTraceHessian (Tower.UnitLatticeL2.edgePos L)
            (Tower.AbelianFieldDensity.massiveOp (L := L)) z
            (x : InfiniteLattice.AmbientSpace) e e'
end YangMills.Construction.Tower.AbelianFieldDensity
end
