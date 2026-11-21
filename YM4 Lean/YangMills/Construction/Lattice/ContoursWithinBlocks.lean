import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlocksAndCorridors
import YangMills.Construction.Lattice.ContourPaths
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def ContoursWithinBlockStatement : Prop :=
  ∀ L m K i : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → i < K →
    ∀ (y : SiteAtLevel L m K (i + 1)) (x : SiteAtLevel L m K i), (x : FourTorus L m) ∈ unitBlock y →
      ∀ Γ ∈ contourSet y x,
        (∀ z : SiteAtLevel L m K i,
          (z = y.toSublattice (levelDepth K i) ∨ z = x ∨ ∃ b ∈ Γ, z = b.source ∨ z = b.target) →
            (z : FourTorus L m) ∈ unitBlock y) ∧
        ∀ b ∈ Γ, b ∈ (bondsInside (unitBlock y) : Set (BondAtLevel L m K i))
end PeriodicLattice
end YangMills.Construction
