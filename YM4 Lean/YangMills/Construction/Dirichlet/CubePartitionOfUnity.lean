import YangMills.Construction.Dirichlet.CentresNearBumps
import YangMills.Construction.WeightedGreen.ExpansionConstants
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
open YangMills.Construction.Torus YangMills.Construction.Dirichlet
noncomputable section
namespace YangMills.Construction.Dirichlet.PartitionOfUnity
variable {d L : ℕ} {S aLow aHigh : ℝ} (B : BlockSetting d L aLow aHigh S)
def outsidePrevDomain (n : ℕ) : Set (PeriodicTorus d S) :=
  cubeComplement ((B.M : ℝ) * B.scaleAt ((n : ℤ) - 1)) (B.domainAt ((n : ℤ) - 1))
structure CubePlacement : Prop where
  disjoint_outside : ∀ n, ∀ Q ∈ B.coverCubesAt n, Disjoint (B.cubePoints Q) (outsidePrevDomain B n)
  disjoint_two_above : ∀ n, ∀ Q ∈ B.coverCubesAt n, Disjoint (B.cubePoints Q) (B.Ω (n + 2))
  union_of_finer_cubes : ∀ n, ∀ Q ∈ B.coverCubesAt n,
    YangMills.Construction.Torus.IsCubeUnion (B.scaleAt ((n : ℤ) + 1)) (B.cubePoints Q)
  region : ∀ n, ∀ Q ∈ B.coverCubesAt n, B.IsCellUnion (B.innerRegion Q)
  contains_closed_cubes : ∀ n, ∀ Q ∈ B.coverCubesAt n, ∀ (c : PeriodicTorus d S) (s : ℝ), 0 < s →
    cubeAt c s ⊆ B.cubePoints Q ∩ B.Ω 0 → cubeAt c s ⊆ B.innerRegion Q
  contains_sites : ∀ n, ∀ Q ∈ B.coverCubesAt n, ∀ x : LatticeSite d S B.ξ,
    (x : PeriodicTorus d S) ∈ B.cubePoints Q ∩ B.Ω 0 → (x : PeriodicTorus d S) ∈ B.innerRegion Q
  region_eq_points : ∀ n, 1 ≤ n → ∀ Q ∈ B.coverCubesAt n, B.innerRegion Q = B.cubePoints Q
structure BumpProperties : Prop where
  few_nonzero : ∀ p : PeriodicTorus d S,
    {Q | Q ∈ B.coverCubes ∧ B.cubeBump Q p ≠ 0}.encard ≤
      (YangMills.Construction.WeightedGreen.cubeOverlap d : ℕ∞)
  squares_between : ∀ p ∈ B.baseNbhd,
    1 ≤ B.bumpSqSum p ∧ B.bumpSqSum p ≤ (YangMills.Construction.WeightedGreen.cubeOverlap d : ℝ)
  smooth_near : ∃ V : Set (PeriodicTorus d S), IsOpen V ∧ B.baseNbhd ⊆ V ∧
    (∀ p ∈ V, 0 < B.bumpSqSum p) ∧
    ∀ Q ∈ B.coverCubes,
      ContDiffOn ℝ ∞ (fun v : Fin d → ℝ => B.partitionOfUnity Q (torusProj d S v))
        (torusProj d S ⁻¹' V) ∧
      ∀ p ∈ V, 0 ≤ B.partitionOfUnity Q p ∧ B.partitionOfUnity Q p ≤ 1
  squares_sum_one : ∀ p ∈ B.baseNbhd,
    ∑ᶠ Q ∈ B.coverCubes, B.partitionOfUnity Q p ^ 2 = 1
  zero_far_from_centre : ∀ Q ∈ B.coverCubes, ∀ p : PeriodicTorus d S,
    2 / 3 * B.blockWidth Q.level < supNorm (p - Q.centre) → B.partitionOfUnity Q p = 0
structure CutoffDiffBounds (c : ℝ) : Prop where
  diff_at_bond : ∀ Q ∈ B.coverCubes, ∀ x x' : LatticeSite d S B.ξ,
    (x : PeriodicTorus d S) ∈ B.baseNbhd →
    supSetDist {(x : PeriodicTorus d S)} (B.Ω 0) ≤ ENNReal.ofReal (3 * B.ξ) → IsNeighbor x x' →
    |B.latticeCutoff Q x' - B.latticeCutoff Q x| ≤ c * (L : ℝ) ^ 2 * B.ξ / ((B.M : ℝ) * B.localScale x)
  laplacian_at_site : ∀ Q ∈ B.coverCubes, ∀ x : LatticeSite d S B.ξ,
    (x : PeriodicTorus d S) ∈ B.baseNbhd →
    supSetDist {(x : PeriodicTorus d S)} (B.Ω 0) ≤ ENNReal.ofReal (3 * B.ξ) →
    |latticeLaplacian (B.latticeCutoff Q) x| ≤ c * (L : ℝ) ^ 4 / ((B.M : ℝ) * B.localScale x) ^ 2
  diff_near_centre : ∀ Q ∈ B.coverCubes, ∀ y ∈ B.centres,
    ∀ x x' : LatticeSite d S B.ξ,
    supNorm ((x : PeriodicTorus d S) - y) ≤ 3 * B.centreSpacing y →
    supNorm ((x' : PeriodicTorus d S) - y) ≤ 3 * B.centreSpacing y →
    |B.latticeCutoff Q x - B.latticeCutoff Q x'| ≤
      c * (L : ℝ) ^ 2 * siteLOneDist x x' / ((B.M : ℝ) * B.centreSpacing y)
  deriv_near_centre : ∀ Q ∈ B.coverCubes, ∀ y ∈ B.centres,
    ∀ x x' : LatticeSite d S B.ξ,
    supNorm ((x : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y →
    supNorm ((x' : PeriodicTorus d S) - y) ≤ 2 * B.centreSpacing y → ∀ μ : Fin d,
    |forwardDiff μ (B.latticeCutoff Q) x - forwardDiff μ (B.latticeCutoff Q) x'| ≤
      c * (L : ℝ) ^ 4 * siteLOneDist x x' / ((B.M : ℝ) * B.centreSpacing y) ^ 2
structure CentresNearCube : Prop where
  level_near : ∀ n, ∀ Q ∈ B.coverCubesAt n, ∀ y ∈ B.centresNearBump Q,
    (B.centreIndex y : ℤ) = (n : ℤ) - 1 ∨ B.centreIndex y = n ∨ B.centreIndex y = n + 1
  cell_inside : ∀ n, ∀ Q ∈ B.coverCubesAt n, ∀ y ∈ B.centresNearBump Q, B.cell y ⊆ B.innerRegion Q
  interior_centre : ∀ n, ∀ Q ∈ B.coverCubesAt n, ∀ y ∈ B.centresNearBump Q,
    B.IsInteriorCentre (B.innerRegion Q) y
  near_sites_inside : ∀ n, ∀ Q ∈ B.coverCubesAt n, ∀ y ∈ B.centresNearBump Q,
    ∀ x : LatticeSite d S B.ξ, (x : PeriodicTorus d S) ∈ B.Ω 0 →
    supNorm ((x : PeriodicTorus d S) - y) ≤ 4 * B.centreSpacing y →
    (x : PeriodicTorus d S) ∈ B.innerRegion Q ∧
      ¬ ∃ b : LatticeBond d S B.ξ, IsBoundaryBond (B.innerRegion Q) b ∧
        b ∉ externalBoundaryBonds (B.Ω 0) (B.innerRegion Q) ∧ (b.source = x ∨ b.target = x)
  few_cubes : ∀ y ∈ B.centres,
    {Q | Q ∈ B.coverCubes ∧ y ∈ B.centresNearBump Q}.encard ≤
      (YangMills.Construction.WeightedGreen.cubeOverlap d : ℕ∞)
def HoldsWithConst (d : ℕ) (c : ℝ) : Prop :=
  ∀ (L : ℕ) (aLow aHigh : ℝ), Parameters d L aLow aHigh →
    ∀ (S : ℝ) (B : BlockSetting d L aLow aHigh S),
      3 * L * (L + 12) ≤ B.M → L * (L + 9) ≤ B.R₁ * B.M →
      CubePlacement B ∧ BumpProperties B ∧ CutoffDiffBounds B c ∧ CentresNearCube B
def partitionConst (d : ℕ) : ℝ := Classical.epsilon (HoldsWithConst d)
def PartitionClaim : Prop := ∀ d : ℕ, HoldsWithConst d (partitionConst d)
end YangMills.Construction.Dirichlet.PartitionOfUnity
