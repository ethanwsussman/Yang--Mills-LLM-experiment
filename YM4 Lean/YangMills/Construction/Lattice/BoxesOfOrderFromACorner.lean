import YangMills.Construction.Averaging.LayerwiseAveragingStandingData
import YangMills.Construction.Lattice.BoxesOfOrder
import YangMills.Construction.Lattice.BoxesOfSitesFromACorner
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K j : ℕ}
def IsSmallCountVector (k : Fin 4 → ℕ) : Prop := ∀ μ, k μ ∈ ({1, 2, 3} : Set ℕ)
def cornerBox (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) : Set (SiteAtLevel L m K j) :=
  sitesFromCorner s fun μ => (k μ : ℤ)
def IsCornerBox (P : Set (SiteAtLevel L m K j)) : Prop :=
  ∃ (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ), IsSmallCountVector k ∧ P = cornerBox s k
def unitNeighbourhood (y : SiteAtLevel L m K j) : Set (SiteAtLevel L m K j) :=
  {x | toLevelUnits L K j
    (TorusMetric.torusSupNorm ((x : FourTorus L m) - (y : FourTorus L m))) ≤ 1}
def blockRange (l k : ℕ) : Set ℤ :=
  {t | -((l : ℤ) - 1) ≤ 2 * t ∧ 2 * t ≤ 2 * (((k : ℤ) - 1) * (l : ℤ)) + ((l : ℤ) - 1)}
def blockRanges (l : ℕ) (k : Fin 4 → ℕ) : Set (Fin 4 → ℤ) :=
  pi univ fun μ => blockRange l (k μ)
def cornerOffsetSite (i : ℕ) (s : SiteAtLevel L m K j) (t : Fin 4 → ℤ) : SiteAtLevel L m K i :=
  offsetSite (s.toSublattice (levelDepth K i)) t
def cornerBlockBox (i : ℕ) (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) :
    Set (SiteAtLevel L m K i) :=
  cornerOffsetSite i s '' blockRanges (L ^ (j - i)) k
def CornerBoxIsOrderBox (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) : Prop :=
  IsOrderBox K j (cornerBox s k) ∧ ∀ μ, coordCount μ (cornerBox s k) = (k μ : ℕ∞)
def SmallSetsAreCornerBoxes (L m K j : ℕ) : Prop :=
  (∀ y : SiteAtLevel L m K j, IsCornerBox ({y} : Set (SiteAtLevel L m K j))) ∧
  (∀ b : BondAtLevel L m K j, IsCornerBox ({b.source, b.target} : Set (SiteAtLevel L m K j))) ∧
  (∀ p : PlaquetteAtLevel L m K j, IsCornerBox p.vertices) ∧
  ∀ y : SiteAtLevel L m K j,
    (unitNeighbourhood y).ncard = 3 ^ 4 ∧ IsCornerBox (unitNeighbourhood y)
def CornerBoxBlocks (i : ℕ) (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ) : Prop :=
  blockUnionAtLevel i (cornerBox s k) = sitesAsTorusPoints (cornerBlockBox i s k) ∧
  InjOn (cornerOffsetSite i s) (blockRanges (L ^ (j - i)) k) ∧
  (∀ μ, (blockRange (L ^ (j - i)) (k μ)).ncard = k μ * L ^ (j - i) ∧
    k μ * L ^ (j - i) ≤ 3 * L ^ (j - i) ∧ 3 * L ^ (j - i) < L ^ (m + K - i)) ∧
  (∀ (y : SiteAtLevel L m K i) (μ : Fin 4), (axisLine y μ).ncard = 2 * L ^ (m + K - i)) ∧
  IsSiteBox (levelDepth K i) (cornerBlockBox i s k)
def OrderBoxesFromCorners : Prop :=
  ∀ L K m : ℕ, Averaging.LayerwiseParameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary
      (torusSide L m) → ∀ j : ℕ, j ≤ K →
    (∀ (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ), IsSmallCountVector k →
      CornerBoxIsOrderBox s k) ∧
    SmallSetsAreCornerBoxes L m K j ∧
    (∀ P : Set (SiteAtLevel L m K j), IsOrderBox K j P → P.Nonempty → IsCornerBox P) ∧
    ∀ i : ℕ, i ≤ j → ∀ (s : SiteAtLevel L m K j) (k : Fin 4 → ℕ), IsSmallCountVector k →
      CornerBoxBlocks i s k
end PeriodicLattice
end YangMills.Construction
