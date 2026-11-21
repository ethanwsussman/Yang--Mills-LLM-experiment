import YangMills.Construction.Averaging.LayerwiseAveragingStandingData
import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.OneStepSchemes
import YangMills.Construction.Lattice.SiteCoordinates
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K i : ℕ}
def axialPathBond (c : BondAtLevel L m K (i + 1)) (μ : Fin 4) (s : ℕ) : BondAtLevel L m K i :=
  Bond.forwardFrom (c.source.toSublattice (levelDepth K i) + (s : ℤ) • unitStep L m (levelDepth K i) μ) μ
def BlockCoordinateForm (y : SiteAtLevel L m K (i + 1)) : Prop :=
  unitBlock y = {x : FourTorus L m | ∃ n : Fin 4 → ℤ, (∀ ν, |n ν| ≤ centreToFaceSteps L) ∧
    x = (offsetSite (y.toSublattice (levelDepth K i)) n : SiteAtLevel L m K i)}
def LiesInEndBlockOrCorridor (c : BondAtLevel L m K (i + 1)) (b : BondAtLevel L m K i) : Prop :=
  b.LiesIn (sitesInBlock (levelDepth K i) c.source) ∨ b.LiesIn (sitesInBlock (levelDepth K i) c.target) ∨
    b ∈ (bondCorridor c : Set (BondAtLevel L m K i))
structure AxialPathCorridorProperties (c : BondAtLevel L m K (i + 1)) (μ : Fin 4) : Prop where
  target_eq : c.target.toSublattice (levelDepth K i) =
    c.source.toSublattice (levelDepth K i) + (L : ℤ) • unitStep L m (levelDepth K i) μ
  source_block : BlockCoordinateForm (i := i) c.source
  target_block : BlockCoordinateForm (i := i) c.target
  blocks_disjoint : Disjoint (unitBlock c.source) (unitBlock c.target)
  axialPath_eq : axialPath (c.source.toSublattice (levelDepth K i)) (c.target.toSublattice (levelDepth K i)) =
    (List.range L).map (axialPathBond c μ)
  liesIn_source_block : ∀ s : ℕ, s < L → (s : ℤ) < centreToFaceSteps L →
    (axialPathBond c μ s).LiesIn (sitesInBlock (levelDepth K i) c.source)
  liesIn_target_block : ∀ s : ℕ, s < L → centreToFaceSteps L < (s : ℤ) →
    (axialPathBond c μ s).LiesIn (sitesInBlock (levelDepth K i) c.target)
  mem_bondCorridor_iff : ∀ s : ℕ, s < L →
    (axialPathBond c μ s ∈ (bondCorridor c : Set (BondAtLevel L m K i)) ↔
      (s : ℤ) = centreToFaceSteps L)
  pivot_eq : (pivot c : BondAtLevel L m K i) =
    axialPathBond c μ (centreToFaceSteps L).toNat
  bondCorridor_eq : (bondCorridor c : Set (BondAtLevel L m K i)) =
    {b | ∃ u : Fin 4 → ℤ, u μ = 0 ∧ (∀ ν, |u ν| ≤ centreToFaceSteps L) ∧
      b = Bond.forwardFrom (offsetSite (c.source.toSublattice (levelDepth K i)) u +
        centreToFaceSteps L • unitStep L m (levelDepth K i) μ) μ}
  corridor_bond_target : ∀ u : Fin 4 → ℤ, u μ = 0 → (∀ ν, |u ν| ≤ centreToFaceSteps L) →
    offsetSite (c.source.toSublattice (levelDepth K i)) u +
        centreToFaceSteps L • unitStep L m (levelDepth K i) μ + unitStep L m (levelDepth K i) μ =
      offsetSite (c.target.toSublattice (levelDepth K i)) u -
        centreToFaceSteps L • unitStep L m (levelDepth K i) μ
  doubleBlock_bond_cover : ∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K i)),
    LiesInEndBlockOrCorridor c b ∨ LiesInEndBlockOrCorridor c b.opposite
def LiesInSomeBlockOrCorridor (b : BondAtLevel L m K i) : Prop :=
  (∃ y : SiteAtLevel L m K (i + 1), b.LiesIn (sitesInBlock (levelDepth K i) y)) ∨
    ∃ c : BondAtLevel L m K (i + 1), c.IsPositivelyOriented ∧ b ∈ (bondCorridor c : Set (BondAtLevel L m K i))
def DoubleBlockGeometryClaim : Prop :=
  ∀ L K m : ℕ, Averaging.LayerwiseParameters 4 2 L K m Matrices.ComplexMatrix2.specialUnitary (torusSide L m) →
    ((centreToFaceSteps L : ℤ) : ℝ) = Averaging.LayerwiseParameters.halfFactor L ∧
    ∀ i : ℕ, i < K →
      (∀ (c : BondAtLevel L m K (i + 1)) (μ : Fin 4),
        c.target - c.source = unitStep L m (levelDepth K (i + 1)) μ → AxialPathCorridorProperties c μ) ∧
      ∀ b : BondAtLevel L m K i,
        LiesInSomeBlockOrCorridor (K := K) (i := i) b ∨
          LiesInSomeBlockOrCorridor (K := K) (i := i) b.opposite
end PeriodicLattice
end YangMills.Construction
