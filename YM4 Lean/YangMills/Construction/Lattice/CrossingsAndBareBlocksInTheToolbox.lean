import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOnUnionsOfBlocks
import YangMills.Construction.Lattice.BoxesOfOrder
import YangMills.Construction.Lattice.OneStepCovarianceAndDomainsInTheToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockCardAndCrossingPrefixes (L m K : ℕ) : Prop :=
  ∀ n : ℕ, n < K → ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
    Nat.card ↥(sitesInBlock (levelDepth K n) c.source : Set (SiteAtLevel L m K n)) = L ^ 4 ∧
    ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      (crossingPath c x).Nodup ∧
      ∀ b ∈ crossingPath c x, ∃ Γ₁ Γ₂ : List (BondAtLevel L m K n),
        crossingPath c x = Γ₁ ++ b :: Γ₂ ∧ axialPath x b.source = Γ₁ ∧
          IsBondPathFromTo Γ₁ x b.source
def BareBlocksAreSiteBoxes (L m K : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ K →
    (∀ y : SiteAtLevel L m K k,
      IsSiteBox (levelDepth K 0) (blockSitesBelow 0 ({y} : Set (SiteAtLevel L m K k))) ∧
      ∀ μ, coordCount μ (blockSitesBelow 0 ({y} : Set (SiteAtLevel L m K k))) ≤
        ((L ^ k : ℕ) : ℕ∞)) ∧
    ∀ c : BondAtLevel L m K k, c.IsPositivelyOriented →
      IsSiteBox (levelDepth K 0) (blockSitesBelow 0 (bondEnds c)) ∧
      ∀ μ, coordCount μ (blockSitesBelow 0 (bondEnds c)) ≤
        ((2 * L ^ k : ℕ) : ℕ∞)
def BareSiteUniqueSubblock (L m K : ℕ) : Prop :=
  ∀ j : ℕ, j < K → ∀ (z : SiteAtLevel L m K (j + 1)) (x : SiteAtLevel L m K 0),
    x ∈ blockSitesBelow 0 ({z} : Set (SiteAtLevel L m K (j + 1))) →
    ∃ z' ∈ sitesInBlock (levelDepth K j) z,
      x ∈ blockSitesBelow 0 ({z'} : Set (SiteAtLevel L m K j)) ∧
      ∀ z'' : SiteAtLevel L m K j, x ∈ blockSitesBelow 0 ({z''} : Set (SiteAtLevel L m K j)) →
        z'' = z'
def CrossingsAndBareBlocks.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K : ℕ, 0 < m →
    BlockCardAndCrossingPrefixes L m K ∧
    BareBlocksAreSiteBoxes L m K ∧
    BareSiteUniqueSubblock L m K
end PeriodicLattice
end YangMills.Construction
