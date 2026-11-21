import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockAverageAtOpposite : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ j j' : ℤ, 0 ≤ j → j' = j + 1 →
  ∀ (ω : ℝ) (c : Bond L m j), ∀ U ∈ compactGaugeFields L m j',
    blockAverageCase ω U c.opposite = blockAverageCase ω U c ∧
    blockAverageOnPositive ω U c.opposite = (blockAverageOnPositive ω U c)⁻¹
end PeriodicLattice
end YangMills.Construction
end
