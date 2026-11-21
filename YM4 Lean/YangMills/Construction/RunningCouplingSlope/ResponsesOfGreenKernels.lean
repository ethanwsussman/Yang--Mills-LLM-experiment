import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.OperatorsOfAStepAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Topology
namespace YangMills.Construction.RunningCouplingSlope
def GreenFamilyResponses : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (h : FlatLinearization.BondKernel) (hl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ)
      (G : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond (n * L) → ℝ)
      (Gl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ),
      FlatLinearization.IsFlowKernel h → FlatLinearization.TendstoLatticeKernel h hl →
        FlatLinearization.IsGreenFamily a L h hl G Gl →
        FlatLinearization.IsResponseSequence a L h (FlatLinearization.responseOfInverse a L G)
          (FlatLinearization.latticeResponseOfInverse a L Gl)
end YangMills.Construction.RunningCouplingSlope
end
