import YangMills.Construction.Lattice.BareUnitsAndLevels
import YangMills.Construction.Lattice.SettingOfASeparatedSequence
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric PeriodicLattice
namespace SupDistance
variable {L m : ℕ}
def supDistScaled (c : ℝ) (x x' : FourTorus L m) : ℝ := c * torusSupNorm (x - x')
def infSupDistScaled (c : ℝ) (X : Set (FourTorus L m)) (x : FourTorus L m) : ℝ :=
  c * (setSupDist ({x} : Set (FourTorus L m)) X).toReal
def IsSupOpen (c : ℝ) (O : Set (FourTorus L m)) : Prop :=
  ∀ x ∈ O, ∃ r : ℝ, 0 < r ∧ ∀ u : FourTorus L m, supDistScaled c u x < r → u ∈ O
def SupDistanceProperties (L m : ℕ) (c : ℝ) : Prop :=
  (∀ x x' : FourTorus L m, supDistScaled c x x' = supDistScaled c x' x) ∧
  (∀ x x' : FourTorus L m, supDistScaled c x x' = 0 → x = x') ∧
  (∀ x x' x'' : FourTorus L m,
    supDistScaled c x x'' ≤ supDistScaled c x x' + supDistScaled c x' x'') ∧
  (∀ O : Set (FourTorus L m),
    IsSupOpen c O ↔ IsOpen (torusProj (torusSide L m) ⁻¹' O)) ∧
  (∀ w x x' : FourTorus L m, |supDistScaled c x w - supDistScaled c x' w| ≤ supDistScaled c x x') ∧
  (∀ X : Set (FourTorus L m), X.Nonempty →
    (∀ x : FourTorus L m, setSupDist ({x} : Set (FourTorus L m)) X ≠ ⊤) ∧
    ∀ x x' : FourTorus L m,
      |infSupDistScaled c X x - infSupDistScaled c X x'| ≤ supDistScaled c x x')
def openLevelCube {K n' : ℕ} (y : SiteAtLevel L m K n') : Set (FourTorus L m) :=
  {u | bareLength L K (torusSupNorm (u - (y : FourTorus L m))) < (L : ℝ) ^ n' / 2}
def LevelLatticesAndCubes (L m K n n' : ℕ) : Prop :=
  (sublattice L m (levelDepth K n') : Set (FourTorus L m)) ⊆ sublattice L m (levelDepth K n) ∧
  (∀ u : FourTorus L m, ∃ Q ∈ levelPartition L m K n', u ∈ Q) ∧
  ∀ y : SiteAtLevel L m K n',
    (∀ u ∈ openLevelCube y, ∀ Q ∈ levelPartition L m K n', u ∈ Q → Q = levelCube y) ∧
    IsOpen (openLevelCube y) ∧
    IsClosed (levelCube y) ∧
    levelCube y = closure (openLevelCube y)
def CubesUnionFinerCubes (L m K n n' : ℕ) : Prop :=
  ∀ Q ∈ levelPartition L m K n', Q = ⋃₀ partitionCubesIn (levelDepth K n) Q
def blockCoords {K n' : ℕ} (n : ℕ) (y : SiteAtLevel L m K n') : Set (FourTorus L m) :=
  {x | ∃ ν : Fin 4 → ℤ, (∀ μ, |(ν μ : ℝ)| ≤ ((L : ℝ) ^ (n' - n) - 1) / 2) ∧
    x = (y : FourTorus L m) + ∑ μ, pointOnAxis L m μ ((ν μ : ℝ) * meshSize L (levelDepth K n))}
def LevelBlocks (L m K n n' : ℕ) : Prop :=
  (∀ y : SiteAtLevel L m K n',
    levelCube y ∩ (sublattice L m (levelDepth K n) : Set (FourTorus L m)) = refinedBlock (n' - n) y ∧
    refinedBlock (n' - n) y = blockCoords n y ∧
    (n = n' → refinedBlock (n' - n) y = siteSingleton y) ∧
    (∀ x ∈ refinedBlock (n' - n) y,
      bareLength L K (torusSupNorm (x - (y : FourTorus L m))) < (L : ℝ) ^ n' / 2) ∧
    ∀ x : SiteAtLevel L m K n,
      (x : FourTorus L m) ∉ regionBoundary (levelDepth K n') (levelCube y)) ∧
  ∀ x : SiteAtLevel L m K n,
    ∃! y' : SiteAtLevel L m K n', (x : FourTorus L m) ∈ refinedBlock (n' - n) y'
def RegionComplements (L m K n n' : ℕ) : Prop :=
  ∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K n') X →
    (∀ C ⊆ levelPartition L m K n', X = ⋃₀ C → C = partitionCubesIn (levelDepth K n') X) ∧
    X ∪ complementRegion (levelDepth K n') X = univ ∧
    (∀ u : FourTorus L m, u ∉ X → u ∈ complementRegion (levelDepth K n') X) ∧
    complementRegion (levelDepth K n') X = closure Xᶜ ∧
    IsPartitionRegion (levelDepth K n) X ∧
    complementRegion (levelDepth K n) X = complementRegion (levelDepth K n') X
def SupDistLatticeFacts : Prop :=
  ∀ (L m : ℕ) (N : SeparatedSequence.Parameters L m) (n n' : ℕ), n ≤ n' → n' ≤ N.K + m →
    (∀ c : ℝ, 0 < c → SupDistanceProperties L m c) ∧
    LevelLatticesAndCubes L m N.K n n' ∧
    CubesUnionFinerCubes L m N.K n n' ∧
    LevelBlocks L m N.K n n' ∧
    RegionComplements L m N.K n n'
end SupDistance
end YangMills.Construction
end
