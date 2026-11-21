import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.FormsOfTheChainAtTheFlatField
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def FlatLinearizationStep : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ h : FlatLinearization.BondKernel, FlatLinearization.IsFlowKernel h →
    ∃ (P : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond n → ℝ)
      (Pl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ),
      FlatLinearization.IsBlockKernel L P Pl ∧
      (∀ᶠ n in Filter.atTop, ∀ [NeZero n] [NeZero L],
        FlatLinearization.IsMinimizerFamily a L (h (n * L)) (P n) ∧
          FlatLinearization.IsPositiveOnTreeGauge (n := n) a L (h (n * L))) ∧
      FlatLinearization.IsFlowKernel (FlatLinearization.renormalizedKernel a L h P)
end YangMills.Construction.RunningCouplingSlope
end
