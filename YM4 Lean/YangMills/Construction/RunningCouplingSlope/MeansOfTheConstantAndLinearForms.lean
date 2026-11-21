import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def ContourAveragesOfConstantAndLinear : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ (ν : Fin 4) (c : TorusLumps.LatticeBond),
      FlatLinearization.latticeContourAverage L
        (fun b => (L : ℝ)⁻¹ * SlopeCoefficient.constantOneForm ν b) c =
        SlopeCoefficient.constantOneForm ν c) ∧
    ∀ c : TorusLumps.LatticeBond,
      FlatLinearization.latticeContourAverage L (FlatLinearization.fineLinearPotential L) c =
        ((c.1 0 : ℤ) : ℝ) * SlopeCoefficient.constantOneForm SlopeCoefficient.secondAxis c
end YangMills.Construction.RunningCouplingSlope
end
