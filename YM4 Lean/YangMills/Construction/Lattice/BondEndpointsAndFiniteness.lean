import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Geometry.TorusMetric
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def Bond.endpointPair {L m : ℕ} {j : ℤ} (b : Bond L m j) : FourTorus L m × FourTorus L m :=
  ((b.source : FourTorus L m), (b.target : FourTorus L m))
def IsLatticeBond (L m : ℕ) (j : ℤ) (p : FourTorus L m × FourTorus L m) : Prop :=
  ∃ b : Bond L m j, b.endpointPair = p
def BondEndpointsAndFiniteness : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ j : ℤ, -((s.m : ℕ) : ℤ) ≤ j →
      (∀ b : Bond s.L s.m j,
        TorusMetric.torusSupNorm ((b.source : FourTorus s.L s.m) - (b.target : FourTorus s.L s.m)) =
          meshSize s.L j) ∧
      (∀ j' : ℤ, -((s.m : ℕ) : ℤ) ≤ j' → j' ≠ j →
        ∀ b : Bond s.L s.m j, ¬IsLatticeBond s.L s.m j' b.endpointPair) ∧
      Finite (Site s.L s.m j) ∧
      Finite (Bond s.L s.m j)) ∧
    (∀ n n' : ℕ, n ≤ s.K → n' ≤ s.K → n ≠ n' →
      ∀ p : FourTorus s.L s.m × FourTorus s.L s.m,
        ¬(IsLatticeBond s.L s.m (levelDepth s.K n) p ∧ IsLatticeBond s.L s.m (levelDepth s.K n') p)) ∧
    (∀ p : FourTorus s.L s.m × FourTorus s.L s.m,
      (∃ n : ℕ, n ≤ s.K ∧ IsLatticeBond s.L s.m (levelDepth s.K n) p) →
        ∃! n : ℕ, n ≤ s.K ∧ IsLatticeBond s.L s.m (levelDepth s.K n) p)
end YangMills.Construction.PeriodicLattice
