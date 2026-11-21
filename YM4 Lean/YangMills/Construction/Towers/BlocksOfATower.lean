import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.SiteCoordinates
import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
section FiniteSide
open YangMills.Construction.PeriodicLattice (FourTorus pointOnAxis unitBlock blockOffsets levelDepth sublattice)
def offsetPoint {L n : ℕ} (a : ℝ) (y : FourTorus L n) (ν : Fin 4 → ℤ) : FourTorus L n :=
  y + ∑ μ, pointOnAxis L n μ ((ν μ : ℝ) * a)
def BondAlongAxis {L n : ℕ} {i : ℤ} (b : PeriodicLattice.Bond L n i) (μ : Fin 4) : Prop :=
  b.target - b.source = PeriodicLattice.unitStep L n i μ ∨
    b.target - b.source = -PeriodicLattice.unitStep L n i μ
def BlockEqOffsetImage (L n k j : ℕ) (y : Vertex L n k j) : Prop :=
  unitBlock y = offsetPoint (meshAt L k (j - 1)) (y : FourTorus L n) '' blockOffsets L 1 ∧
    InjOn (offsetPoint (meshAt L k (j - 1)) (y : FourTorus L n)) (blockOffsets L 1) ∧
    (unitBlock y).ncard = L ^ 4 ∧
    unitBlock y ⊆ (sublattice L n (levelDepth k (j - 1)) : Set (FourTorus L n))
def BlocksPartitionFiner (L n k j : ℕ) : Prop :=
  (∀ y : Vertex L n k j,
    unitBlock y ∩ (sublattice L n (levelDepth k j) : Set (FourTorus L n)) = {(y : FourTorus L n)}) ∧
  (∀ x : Vertex L n k (j - 1), ∃! y : Vertex L n k j, (x : FourTorus L n) ∈ unitBlock y) ∧
  ∀ x : Vertex L n k (j - 1), (x : FourTorus L n) ∉ (sublattice L n (levelDepth k j) : Set (FourTorus L n)) →
    ∃! y : Vertex L n k j, (x : FourTorus L n) ∈ unitBlock y \ {(y : FourTorus L n)}
def BlockShiftAlongBond (L n k j : ℕ) (c : Edge L n k j) (μ : Fin 4) : Prop :=
  BijOn (fun x : FourTorus L n => x + ((c.target : FourTorus L n) - (c.source : FourTorus L n)))
      (unitBlock c.source) (unitBlock c.target) ∧
    ∀ x x' : Vertex L n k (j - 1), (x : FourTorus L n) ∈ unitBlock c.source →
      (x' : FourTorus L n) = (x : FourTorus L n) + ((c.target : FourTorus L n) - (c.source : FourTorus L n)) →
      ((x' : FourTorus L n) - (x : FourTorus L n) = pointOnAxis L n μ ((L : ℝ) * meshAt L k (j - 1)) ∨
        (x' : FourTorus L n) - (x : FourTorus L n) =
          pointOnAxis L n μ (-((L : ℝ) * meshAt L k (j - 1)))) ∧
      (∃ t : ℤ, |t| = (L : ℤ) ∧ PeriodicLattice.IsAxialDisplacement x x' μ t) ∧
      (PeriodicLattice.axialPath x x').length = L ∧
      ∀ b ∈ PeriodicLattice.axialPath x x', BondAlongAxis b μ
def SymmetryMapsBlocks (L n k j : ℕ) : Prop :=
  ∀ f : FourTorus L n → FourTorus L n, IsDistancePreserving f → MapsSublatticeOnto k j f →
    ∀ y : Vertex L n k j, f '' unitBlock y = unitBlock (vertexImage f y : Vertex L n k j)
end FiniteSide
namespace FullSpace
open YangMills.Construction.InfiniteLattice (AmbientSpace)
def offsetPoint (a : ℝ) (y : AmbientSpace) (ν : Fin 4 → ℤ) : AmbientSpace :=
  y + ∑ μ, Pi.single μ ((ν μ : ℝ) * a)
def BondAlongAxis {a : ℝ} (b : InfiniteLattice.Link a) (μ : Fin 4) : Prop :=
  b.terminal - b.initial = InfiniteLattice.axisStep a μ ∨
    b.terminal - b.initial = -InfiniteLattice.axisStep a μ
def BlockEqOffsetImage (L k j : ℕ) (y : Vertex L k j) : Prop :=
  cube L (meshAt L k (j - 1)) y =
      offsetPoint (meshAt L k (j - 1)) (y : AmbientSpace) '' PeriodicLattice.blockOffsets L 1 ∧
    InjOn (offsetPoint (meshAt L k (j - 1)) (y : AmbientSpace))
      (PeriodicLattice.blockOffsets L 1) ∧
    (cube L (meshAt L k (j - 1)) y).ncard = L ^ 4 ∧
    cube L (meshAt L k (j - 1)) y ⊆
      (InfiniteLattice.latticeSubgroup (meshAt L k (j - 1)) : Set AmbientSpace)
def BlocksPartitionFiner (L k j : ℕ) : Prop :=
  (∀ y : Vertex L k j,
    cube L (meshAt L k (j - 1)) y ∩
      (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) = {(y : AmbientSpace)}) ∧
  (∀ x : Vertex L k (j - 1), ∃! y : Vertex L k j,
    (x : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y) ∧
  ∀ x : Vertex L k (j - 1),
    (x : AmbientSpace) ∉ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) →
    ∃! y : Vertex L k j,
      (x : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y \ {(y : AmbientSpace)}
def BlockTranslateAlongBond (L k j : ℕ) (c : Edge L k j) (μ : Fin 4) : Prop :=
  BijOn (fun x : AmbientSpace => x + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)))
      (cube L (meshAt L k (j - 1)) c.initial) (cube L (meshAt L k (j - 1)) c.terminal) ∧
    ∀ x x' : Vertex L k (j - 1), (x : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) c.initial →
      (x' : AmbientSpace) = (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)) →
      ((x' : AmbientSpace) - (x : AmbientSpace) = Pi.single μ ((L : ℝ) * meshAt L k (j - 1)) ∨
        (x' : AmbientSpace) - (x : AmbientSpace) = Pi.single μ (-((L : ℝ) * meshAt L k (j - 1)))) ∧
      (∃ t : ℤ, |t| = (L : ℤ) ∧ IsAxisDisplacement x x' μ t) ∧
      (axisPath x x').length = L ∧
      ∀ b ∈ axisPath x x', BondAlongAxis b μ
def SymmetryMapsBlocks (L k j : ℕ) : Prop :=
  ∀ f : AmbientSpace → AmbientSpace, IsDistancePreserving f → MapsSublatticeOnto (meshAt L k j) f →
    ∀ y : Vertex L k j,
      f '' cube L (meshAt L k (j - 1)) y =
        cube L (meshAt L k (j - 1)) (vertexImage f y : Vertex L k j)
end FullSpace
def BlockStructure : Prop :=
  ∀ L k j : ℕ, Conventions.IsAdmissibleBlockingFactor L → 1 ≤ k → 1 ≤ j → j ≤ k →
    (∀ n : ℕ, 0 < n →
      (∀ y : Vertex L n k j, BlockEqOffsetImage L n k j y) ∧
      BlocksPartitionFiner L n k j ∧
      (∀ (c : Edge L n k j) (μ : Fin 4), BondAlongAxis c μ →
        BlockShiftAlongBond L n k j c μ) ∧
      SymmetryMapsBlocks L n k j) ∧
    (∀ y : FullSpace.Vertex L k j, FullSpace.BlockEqOffsetImage L k j y) ∧
    FullSpace.BlocksPartitionFiner L k j ∧
    (∀ (c : FullSpace.Edge L k j) (μ : Fin 4), FullSpace.BondAlongAxis c μ →
      FullSpace.BlockTranslateAlongBond L k j c μ) ∧
    FullSpace.SymmetryMapsBlocks L k j
end Tower
end YangMills.Construction
end
