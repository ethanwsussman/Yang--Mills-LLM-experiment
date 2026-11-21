import YangMills.Construction.Dirichlet.GreenOperatorEstimates
import YangMills.Construction.Torus.OperatorsOfTheSequence
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted.GreenPointwise
def decayFactor {D : TorusData} (B : SeparatedChain D) (y y' : D.Space) : ℝ :=
  Real.exp (-(1 / 2 * DirichletGreen.FourDimensional.decayRate D.L) * B.weightedDistance y y')
end YangMills.Construction.Weighted.GreenPointwise
end
