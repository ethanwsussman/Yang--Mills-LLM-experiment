import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def MeanRadiusOpposite : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ U ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
    ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented → meanRadius U c.opposite = meanRadius U c
end RunningCouplingSlope
end YangMills.Construction
end
