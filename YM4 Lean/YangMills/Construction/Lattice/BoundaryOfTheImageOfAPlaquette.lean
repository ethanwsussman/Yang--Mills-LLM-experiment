import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def PlaquetteImageBoundary : Prop :=
  ∀ (L m : ℕ) (i j : ℤ) (σ : FourTorus L m ≃ FourTorus L m),
    Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    -(m : ℤ) ≤ i → σ ∈ latticeIsometries L m i → i ≤ j → ∀ p : Plaquette L m j,
      (∀ b ∈ (plaquetteImage σ p).boundaryBonds, ∃ c ∈ p.boundaryBonds,
        b = bondImage σ c ∨ b = (bondImage σ c).opposite) ∧
      ∀ c ∈ p.boundaryBonds, ∃ b ∈ (plaquetteImage σ p).boundaryBonds,
        b = bondImage σ c ∨ b = (bondImage σ c).opposite
end YangMills.Construction.PeriodicLattice
