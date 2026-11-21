import YangMills.Construction.Lattice.ParallelBondsAndSidesOfAPlaquette
import Mathlib
namespace YangMills.Construction.PeriodicLattice
def EdgesPositiveWithEndpointsAtVertices : Prop :=
  ∀ (L m : ℕ) (j : ℤ) (p : Plaquette L m j), ∀ b ∈ p.edges,
    b.IsPositivelyOriented ∧ b.source ∈ p.vertices ∧ b.target ∈ p.vertices
end YangMills.Construction.PeriodicLattice
