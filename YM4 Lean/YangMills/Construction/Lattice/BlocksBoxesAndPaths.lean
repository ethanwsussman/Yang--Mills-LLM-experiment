import YangMills.Construction.Averaging.OneStepToolboxData
import YangMills.Construction.Lattice.BoxesOfSitesFromACorner
import YangMills.Construction.Lattice.LevelCubesAndBlocks
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def halfSideSteps (L i : ℕ) : ℤ := ((L : ℤ) ^ i - 1) / 2
def blockCubeOffsets (L i : ℕ) : Set (Fin 4 → ℤ) := {n | ∀ μ, |n μ| ≤ halfSideSteps L i}
def gridBlockOffsets (L i : ℕ) (q : Fin 4 → ℕ) : Set (Fin 4 → ℤ) :=
  {t | ∀ μ, -halfSideSteps L i ≤ t μ ∧ t μ ≤ (q μ : ℤ) * (L : ℤ) ^ i + halfSideSteps L i}
section Sites
variable {L m : ℕ} {j : ℤ}
def siteGrid (y : Site L m j) (q : Fin 4 → ℕ) : Set (Site L m j) :=
  {z | ∃ p : Fin 4 → ℤ, (∀ μ, 0 ≤ p μ ∧ p μ ≤ (q μ : ℤ)) ∧ z = offsetSite y p}
def siteSegment (y : Site L m j) (μ : Fin 4) (r : ℕ) : Set (Site L m j) :=
  {z | ∃ t : ℕ, t < r ∧ z = y + t • unitStep L m j μ}
def shiftByBlock (i : ℕ) (μ : Fin 4) (x : Site L m j) : Site L m j :=
  x + ((L : ℤ) ^ i) • unitStep L m j μ
def IsBoxOfBlockWidth (j : ℤ) (P : Set (Site L m j)) : Prop :=
  IsSiteBox j P ∧ ∃ N : Fin 4 → ℤ, HasSiteCounts j P N ∧
    ∀ μ, N μ = (L : ℤ) ∨ N μ = 2 * (L : ℤ)
end Sites
def MeshAndHalfSide (L K k i : ℕ) : Prop :=
  meshSize L (levelDepth K k) = (L : ℝ) ^ i * meshSize L (levelDepth K (k - i)) ∧
    2 * halfSideSteps L i + 1 = (L : ℤ) ^ i
def RefinedBlockParametrization (L m K k i : ℕ) : Prop :=
  ∀ y : SiteAtLevel L m K k,
    IsParametrizedBy (y.toSublattice (levelDepth K (k - i))) (blockCubeOffsets L i)
      (refinedBlock i y) ∧
    (refinedBlock i y).ncard = L ^ (4 * i) ∧
    refinedBlock 0 y = {(y : FourTorus L m)}
def RefinedBlocksCoverSublattice (L m K k i : ℕ) : Prop :=
  (univ : Set (SiteAtLevel L m K k)).PairwiseDisjoint (refinedBlock i) ∧
    (⋃ y : SiteAtLevel L m K k, refinedBlock i y) =
      (sublattice L m (levelDepth K (k - i)) : Set (FourTorus L m))
def BlockUnionsOverSites (L m K k : ℕ) : Prop :=
  ∀ Z : Set (SiteAtLevel L m K k),
    blockUnionAtLevel k Z = sitesAsTorusPoints Z ∧
    (∀ n : ℕ, n < k → blockUnionAtLevel n Z =
      ⋃ z ∈ (sitesIn (blockUnionAtLevel (n + 1) Z) : Set (SiteAtLevel L m K (n + 1))), unitBlock z) ∧
    (∀ n : ℕ, n < k → ∀ c : BondAtLevel L m K (n + 1),
      (c.source : FourTorus L m) ∈ blockUnionAtLevel (n + 1) Z →
      (c.target : FourTorus L m) ∈ blockUnionAtLevel (n + 1) Z →
        bondDoubleBlock c ⊆ blockUnionAtLevel n Z) ∧
    ∀ n : ℕ, n ≤ k → ∀ x : SiteAtLevel L m K n, (x : FourTorus L m) ∈ blockUnionAtLevel n Z →
      refinedBlock n x ⊆ blockUnionAtLevel 0 Z
def GridBlocksFormBox (L m K k i : ℕ) : Prop :=
  ∀ (y : SiteAtLevel L m K k) (q : Fin 4 → ℕ), (∀ μ, q μ + 1 < L ^ (m + K - k)) →
    IsSiteBox (levelDepth K (k - i)) (sitesIn (refinedBlockUnion i (siteGrid y q))) ∧
    IsParametrizedBy (y.toSublattice (levelDepth K (k - i))) (gridBlockOffsets L i q)
      (refinedBlockUnion i (siteGrid y q)) ∧
    HasSiteCounts (levelDepth K (k - i)) (sitesIn (refinedBlockUnion i (siteGrid y q)))
      fun μ => ((q μ : ℤ) + 1) * (L : ℤ) ^ i
def StepSetsAreBoxes (L m K n : ℕ) : Prop :=
  (∀ y : SiteAtLevel L m K (n + 1),
    IsBoxOfBlockWidth (levelDepth K n) (sitesIn (unitBlock y))) ∧
  (∀ c : BondAtLevel L m K (n + 1),
    IsBoxOfBlockWidth (levelDepth K n) (sitesIn (bondDoubleBlock c))) ∧
  ∀ p : PlaquetteAtLevel L m K (n + 1),
    IsBoxOfBlockWidth (levelDepth K n) (sitesIn (⋃ y ∈ p.vertices, unitBlock y))
def SegmentBlocksFormBox (L m K k : ℕ) : Prop :=
  ∀ (y : SiteAtLevel L m K k) (μ : Fin 4) (r : ℕ), 1 ≤ r → r ≤ 3 →
    IsSiteBox (levelDepth K 0) (sitesIn (refinedBlockUnion k (siteSegment y μ r))) ∧
    ∃ N : Fin 4 → ℤ,
      HasSiteCounts (levelDepth K 0) (sitesIn (refinedBlockUnion k (siteSegment y μ r))) N ∧
      ∀ ν, N ν ≤ 3 * (L : ℤ) ^ k
def AxialPathsAcrossBond (L m K k i : ℕ) : Prop :=
  ∀ (b : BondAtLevel L m K k) (μ : Fin 4), b.target - b.source = unitStep L m (levelDepth K k) μ →
    BijOn (shiftByBlock i μ) (sitesIn (refinedBlock i b.source) : Set (SiteAtLevel L m K (k - i)))
      (sitesIn (refinedBlock i b.target)) ∧
    ∀ x ∈ (sitesIn (refinedBlock i b.source) : Set (SiteAtLevel L m K (k - i))),
      IsAxialDisplacement x (shiftByBlock i μ x) μ ((L : ℤ) ^ i) ∧
      IsBondPathFromTo (axialPath x (shiftByBlock i μ x)) x (shiftByBlock i μ x) ∧
      (axialPath x (shiftByBlock i μ x)).length = L ^ i ∧
      (∀ b' ∈ axialPath x (shiftByBlock i μ x), b'.IsPositivelyOriented) ∧
      ∀ z ∈ sitesOfPath x (axialPath x (shiftByBlock i μ x)),
        (z : FourTorus L m) ∈ refinedBlock i b.source ∪ refinedBlock i b.target
def DoubleBlockCrossings (L m K n : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
    BijOn (shiftAcross (j' := levelDepth K n) c) (sitesInBlock (levelDepth K n) c.source)
      (sitesInBlock (levelDepth K n) c.target) ∧
    ∀ x ∈ sitesInBlock (levelDepth K n) c.source,
      IsBondPathFromTo (crossingPath c x) x (shiftAcross c x) ∧
      (crossingPath c x).length = L ∧
      ∀ b ∈ crossingPath c x, b.IsPositivelyOriented ∧
        b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K n))
def ContoursInBlock (L m K n : ℕ) (y : SiteAtLevel L m K (n + 1))
    (x : SiteAtLevel L m K n) : Prop :=
  ∀ Γ ∈ contourSet y x, Γ.length ≤ 2 * (L - 1) ∧
    ∀ z ∈ sitesOfPath (y.toSublattice (levelDepth K n)) Γ, z ∈ sitesInBlock (levelDepth K n) y
def CombInBlock (L m K n : ℕ) (y : SiteAtLevel L m K (n + 1)) (o x : SiteAtLevel L m K n) : Prop :=
  (∀ b ∈ coordinateComb o x, b.IsPositivelyOriented) ∧
  (∀ ν, countSteps (coordinateComb o x) (unitStep L m (levelDepth K n) ν) ≤ L - 1) ∧
  (∀ z ∈ sitesOfPath o (coordinateComb o x), z ∈ sitesInBlock (levelDepth K n) y) ∧
  ∀ (Γ₁ Γ₂ : List (BondAtLevel L m K n)) (z : SiteAtLevel L m K n),
    coordinateComb o x = Γ₁ ++ Γ₂ → IsBondPathFromTo Γ₁ o z → coordinateComb o z = Γ₁
def BlockContoursCombsAndBaseSites (L m K n : ℕ) : Prop :=
  (∀ (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n), x ∈ sitesInBlock (levelDepth K n) y →
    ContoursInBlock L m K n y x ∧
    schemeBaseSite .cornered (levelDepth K n) y ∈ sitesInBlock (levelDepth K n) y ∧
    CombInBlock L m K n y (schemeBaseSite .cornered (levelDepth K n) y) x) ∧
  ∀ (c : BondAtLevel L m K (n + 1)) (s : AveragingScheme), c.IsPositivelyOriented →
    schemeBaseSite s (levelDepth K n) c.source ∈ sitesInBlock (levelDepth K n) c.source ∧
    axialPath (schemeBaseSite s (levelDepth K n) c.source) (schemeBaseSite s (levelDepth K n) c.target) =
      crossingPath c (schemeBaseSite s (levelDepth K n) c.source)
def BlocksBoxesPaths.Statement : Prop :=
  ∀ L K m : ℕ, Averaging.OneStep.Parameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary →
    halfSideSteps L 1 = centreToFaceSteps L ∧
    ((halfSideSteps L 1 : ℤ) : ℝ) = Averaging.OneStep.halfBlockingFactor L ∧
    (∀ i k : ℕ, i ≤ k → k ≤ K →
      MeshAndHalfSide L K k i ∧
      RefinedBlockParametrization L m K k i ∧
      RefinedBlocksCoverSublattice L m K k i ∧
      GridBlocksFormBox L m K k i ∧
      AxialPathsAcrossBond L m K k i) ∧
    (∀ i j k : ℕ, j ≤ i → i ≤ k → k ≤ K → RefinedBlockNesting L m K k i j) ∧
    (∀ k : ℕ, k ≤ K → BlockUnionsOverSites L m K k) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ K → SegmentBlocksFormBox L m K k) ∧
    ∀ n : ℕ, n < K →
      StepSetsAreBoxes L m K n ∧
      DoubleBlockCrossings L m K n ∧
      BlockContoursCombsAndBaseSites L m K n
end PeriodicLattice
end YangMills.Construction
