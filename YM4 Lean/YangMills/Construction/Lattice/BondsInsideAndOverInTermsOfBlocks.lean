import YangMills.Construction.Lattice.CoarseBlockCentres
import YangMills.Construction.Lattice.LiftOfOrder
import Mathlib
namespace YangMills.Construction.PeriodicLattice
def BondPositionByBlocks : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j k : ℕ, j ≤ k → k ≤ K → ∀ b : BondAtLevel L m K j,
    (∀ y : SiteAtLevel L m K k,
      (coarseCentre j k b.source = y ∧ coarseCentre j k b.target = y) ↔
        ((b.source : FourTorus L m) ∈ blockAtLevel j y ∧
          (b.target : FourTorus L m) ∈ blockAtLevel j y)) ∧
    (∀ c : BondAtLevel L m K k,
      (coarseCentre j k b.source = c.source ∧ coarseCentre j k b.target = c.target) ↔
        ((b.source : FourTorus L m) ∈ blockAtLevel j c.source ∧
          (b.target : FourTorus L m) ∈ blockAtLevel j c.target)) ∧
    ((∃ y : SiteAtLevel L m K k, IsInsideBlockAt j y b) ∨
      ∃ c : BondAtLevel L m K k, CoversBond c b)
end YangMills.Construction.PeriodicLattice
