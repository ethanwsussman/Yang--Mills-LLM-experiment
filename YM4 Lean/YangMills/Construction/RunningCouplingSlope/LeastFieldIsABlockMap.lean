import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.RunningCouplingSlope.BlockMaps
import YangMills.Construction.RunningCouplingSlope.LogarithmOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MinimizerIsBlockMap : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ (t : ℕ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∃ (P : (n : ℕ) → TorusFields.TorusBond (n * L) → TorusFields.TorusBond n → ℝ)
      (Pl : TorusLumps.LatticeBond → TorusLumps.LatticeBond → ℝ),
      SlopeCoefficient.IsBlockMap L (SlopeCoefficient.minimizerOnFinerTorus a ρ L t) P Pl
end YangMills.Construction.RunningCouplingSlope
end
