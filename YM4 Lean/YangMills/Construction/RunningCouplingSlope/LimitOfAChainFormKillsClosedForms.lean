import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open FlatLinearization TorusLumps
def flowKernelLimitAnnihilatesClosedStatement : Prop :=
  ∀ (h : BondKernel) (hl : LatticeBond → LatticeBond → ℝ), IsFlowKernel h → TendstoLatticeKernel h hl →
    (∃ M θ : ℝ, 0 < θ ∧ ∀ b c : LatticeBond,
      |hl b c| ≤ M * Real.exp (-(θ * SlopeCoefficient.offsetNormReal (b.1 - c.1)))) ∧
    (∀ (ν : Fin 4) (b : LatticeBond), HasSum (fun c => hl b c * SlopeCoefficient.constantOneForm ν c) 0) ∧
    (∀ φ : (Fin 4 → ℤ) → ℝ, SlopeCoefficient.HasPolynomialGrowth φ → ∀ b : LatticeBond,
      HasSum (fun c => hl b c * SlopeCoefficient.latticeGradient φ c) 0) ∧
    ∀ b : LatticeBond, HasSum (fun c => hl b c *
      (((c.1 0 : ℤ) : ℝ) * SlopeCoefficient.constantOneForm SlopeCoefficient.secondAxis c)) 0
end YangMills.Construction.RunningCouplingSlope
end
