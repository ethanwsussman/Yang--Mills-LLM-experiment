import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlockAveraging
import Mathlib
namespace YangMills.Construction.PeriodicLattice
def ContourBondsInDoubleBlock : Prop :=
  ∀ L m K n : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → n < K →
    ∀ c : BondAtLevel L m K (n + 1),
      ∀ y : SiteAtLevel L m K (n + 1), y = c.source ∨ y = c.target →
        ∀ x ∈ sitesInBlock (levelDepth K n) y, ∀ Γ ∈ contourSet y x,
          ∀ b ∈ Γ, b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
end YangMills.Construction.PeriodicLattice
