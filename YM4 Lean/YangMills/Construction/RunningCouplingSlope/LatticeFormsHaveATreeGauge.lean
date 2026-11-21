import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open Conventions FlatLinearization
def latticeTreeGaugeStatement : Prop :=
  ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ ξ : LatticeOneForm, ∃ φ : (Fin 4 → ℤ) → ℝ,
    VanishesOnLatticeTrees L (fun b => ξ b + SlopeCoefficient.latticeGradient φ b) ∧
    ((∃ C, ∀ b, |ξ b| ≤ C) → ∃ C, ∀ z, |φ z| ≤ C) ∧
    (FlatLinearization.HasPolynomialGrowth ξ →
      SlopeCoefficient.HasPolynomialGrowth φ ∧
        FlatLinearization.HasPolynomialGrowth (SlopeCoefficient.latticeGradient φ)) ∧
    ∀ c, latticeContourAverage L (SlopeCoefficient.latticeGradient φ) c = 0
end YangMills.Construction.RunningCouplingSlope
end
