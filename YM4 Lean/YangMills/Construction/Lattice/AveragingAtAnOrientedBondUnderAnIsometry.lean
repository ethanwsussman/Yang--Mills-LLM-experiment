import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockAverageCommutesWithIsometries : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ i : ℤ, -(m : ℤ) ≤ i → ∀ σ ∈ latticeIsometries L m i,
  ∀ j j' : ℤ, i ≤ j → 0 ≤ j → j' = j + 1 →
  ∀ (ω : ℝ) (c : Bond L m j), ∀ U ∈ compactGaugeFields L m j',
    (DoubleBlockPlaquettesNear ω (bondImage σ c) (transportGaugeField σ U) ↔
        DoubleBlockPlaquettesNear ω c U) ∧
    blockAverageCase ω (transportGaugeField σ U) (bondImage σ c) = blockAverageCase ω U c ∧
    blockAverageOnPositive ω (transportGaugeField σ U) (bondImage σ c) =
      blockAverageOnPositive ω U c
end PeriodicLattice
end YangMills.Construction
end
