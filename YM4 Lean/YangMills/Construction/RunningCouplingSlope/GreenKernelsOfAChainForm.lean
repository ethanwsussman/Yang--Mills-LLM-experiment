import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
open Conventions FlatLinearization TorusFields TorusLumps
def greenKernelsExistStatement : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L →
    ∀ (h : BondKernel) (hl : LatticeBond → LatticeBond → ℝ),
    IsFlowKernel h → TendstoLatticeKernel h hl →
    ∃ (G : (n : ℕ) → TorusBond (n * L) → TorusBond (n * L) → ℝ) (Gl : LatticeBond → LatticeBond → ℝ),
      IsGreenFamily a L h hl G Gl
end YangMills.Construction.RunningCouplingSlope
end
