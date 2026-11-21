import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def InnerBondsReachEndpoint : Prop :=
  ∀ (L m : ℕ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ (i : ℤ) (K k e r : ℕ)
    (Ω : ℕ → Set (FourTorus L m)), IsChainFromIndex K k i Ω →
      IsSeparatedChain K e r 0 k Ω →
      ∀ b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)),
        ∃ a : SiteAtLevel L m K 0, IsEndpointOf (activeBondSet K k Ω) (a : FourTorus L m) ∧
          Relation.ReflTransGen
            (fun x y : SiteAtLevel L m K 0 =>
              ∃ c ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)), c.source = x ∧ c.target = y)
            a b.source
end YangMills.Construction.PeriodicLattice
