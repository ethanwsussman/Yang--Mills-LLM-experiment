import YangMills.Construction.RunningCouplingSlope.SoftChainOnATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace RunningCouplingSlope
def HolDifferentialAtOneEqSmoothing : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ n k j : ℕ, 0 < n → j < k →
    ∀ B ∈ Tower.complexEdgeForms L n k j,
    ∀ c : Tower.Edge L n k (j + 1), c.IsPositivelyOriented →
      Tower.holLeftDifferential normalizedMean (fun _ => 1) B c = Tower.linearSmoothing L n k j B c
end RunningCouplingSlope
end YangMills.Construction
end
