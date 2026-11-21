import YangMills.Construction.BackgroundField.FloorOnTheProductOfTheGapAndBlockNumbers
import Mathlib
import YangMills.Construction.ClusterExpansion.AbsoluteFloorOfTheChainOfRates
import YangMills.Construction.Lattice.FloorOnTheWidthTimesTheRate
import YangMills.Construction.Lattice.ThresholdOfTheCountOfDomainsThroughABond
import YangMills.Construction.Parameters.OrderOfChoice
set_option autoImplicit false


noncomputable section
namespace YangMills.Construction.BracketSystems
def maxMultiplicity : ℕ := 4 ^ 4 + 27 ^ 4 + 1
end YangMills.Construction.BracketSystems
end

noncomputable section
namespace YangMills.Construction.BracketSystems
def marginExponentialFloor : ℝ :=
  Real.exp (16 + (23 + (maxMultiplicity : ℝ)) * Real.log 2)
end YangMills.Construction.BracketSystems
end

noncomputable section
namespace YangMills.Construction.ParameterChoice
structure MatchesThresholds (N : ExternalConstants) : Prop where
  blockFloor_isUniform : PeriodicLattice.UniformRateChainThreshold.IsUniformThreshold N.blockFloor
  productFloor_above : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    BackgroundField.GapBlockProductFloor.AboveThresholds L (N.productFloor L)
  Cδ_ge : PeriodicLattice.WidthRateFloor.domainSumRateFloor ≤ N.Cδ
  remainderConst_ge : ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    BracketSystems.marginExponentialFloor ≤ N.remainderConst L
  κAnalytic_threshold : PeriodicLattice.IsDomainCountThreshold N.κAnalytic
end YangMills.Construction.ParameterChoice
end
