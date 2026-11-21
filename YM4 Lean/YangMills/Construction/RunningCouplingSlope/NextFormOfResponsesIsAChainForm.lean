import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def RenormalizedKernelIsFlowKernel : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (h : FlatLinearization.BondKernel)
      (P : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond n → ℝ)
      (Pl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ),
      FlatLinearization.IsFlowKernel h → FlatLinearization.IsResponseSequence a L h P Pl →
        FlatLinearization.IsFlowKernel (FlatLinearization.renormalizedKernel a L h P)
end YangMills.Construction.RunningCouplingSlope
end
