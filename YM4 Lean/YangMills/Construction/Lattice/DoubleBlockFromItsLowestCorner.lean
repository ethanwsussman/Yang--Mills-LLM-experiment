import YangMills.Construction.Lattice.BoxesOfSitesFromACorner
import YangMills.Construction.Lattice.OneStepSchemes
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K n : ℕ}
def cornerQuadruples (L : ℕ) (μ : Fin 4) : Set (Fin 4 → ℤ) :=
  {r | 0 ≤ r μ ∧ r μ ≤ 2 * (L : ℤ) - 1 ∧ ∀ ν, ν ≠ μ → 0 ≤ r ν ∧ r ν ≤ (L : ℤ) - 1}
def DifferByUnitVector (r r' : Fin 4 → ℤ) : Prop :=
  ∃ ν : Fin 4, r' - r = Pi.single ν 1 ∨ r' - r = -Pi.single ν 1
def DoubleBlockCornerCoordinates (c : BondAtLevel L m K (n + 1)) (μ : Fin 4) : Prop :=
  let o : SiteAtLevel L m K n := schemeBaseSite .cornered (levelDepth K n) c.source
  let Q := cornerQuadruples L μ
  (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) = offsetSite o '' Q ∧
  (∀ x ∈ (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)),
    ∃! r, r ∈ Q ∧ x = offsetSite o r) ∧
  (sitesIn (unitBlock c.source) : Set (SiteAtLevel L m K n)) =
    offsetSite o '' {r | r ∈ Q ∧ r μ ≤ (L : ℤ) - 1} ∧
  (sitesIn (unitBlock c.target) : Set (SiteAtLevel L m K n)) =
    offsetSite o '' {r | r ∈ Q ∧ (L : ℤ) ≤ r μ} ∧
  ∀ r ∈ Q, ∀ r' ∈ Q,
    (∃ b : BondAtLevel L m K n, b.source = offsetSite o r ∧
      b.target = offsetSite o r') ↔ DifferByUnitVector r r'
def DoubleBlockFromLowestCorner : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → ∀ n : ℕ, n < K →
    ∀ (c : BondAtLevel L m K (n + 1)) (μ : Fin 4), c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
      DoubleBlockCornerCoordinates c μ ∧
      IsSiteBox (levelDepth K n) (sitesIn (bondDoubleBlock c)) ∧
      HasSiteCounts (levelDepth K n) (sitesIn (bondDoubleBlock c)) (doubledCounts (L : ℤ) μ)
end PeriodicLattice
end YangMills.Construction
