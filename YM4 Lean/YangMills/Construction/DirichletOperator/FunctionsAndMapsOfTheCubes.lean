import YangMills.Construction.DirichletOperator.SeparatedSequenceOfThePropagator
import YangMills.Construction.PartitionCubes.LocalOperators
import YangMills.Construction.RegionSequence.SeparatedNestedRegions
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.PartitionCubes
open RegionSequence.NestedRegions (curlTorusAdj curlTorus dTorus dTorusAdj rangeProj complProj
  bondLap bondInner tensorInner AnchoredIn)
def shiftedClassWindow (N : ℤ) (u : ℝ) : Set ℝ :=
  {v | (∃ i : ℤ, v = u + i) ∧ -((N : ℝ) / 2) ≤ v ∧ v < (N : ℝ) / 2}
structure BumpsExist : Prop where
  exists_profile : ∃ f, IsSqPartitionBump f
  exists_mollifier : ∃ f, IsMollifierBump f
  sum_over_window : ∀ N : ℤ, 2 ≤ N → ∀ u : ℝ,
    ∑ᶠ v ∈ shiftedClassWindow N u, sqPartitionBump v ^ 2 = 1
def physicalTorusPoint (L m : ℕ) (p : Fin 4 → ℝ) : PeriodicLattice.FourTorus L m :=
  fun μ => (p μ : AddCircle (PeriodicLattice.torusSide L m))
def levelUnitsPoint (𝒮 : RegionSequence.NestedRegions) (K : ℕ) (p : Fin 4 → ℝ) : 𝒮.Point :=
  Torus.torusProj 4 𝒮.side fun μ => PeriodicLattice.toLevelUnits 𝒮.L K 𝒮.s (p μ)
structure CubeGridAtLevel (𝒮 : RegionSequence.NestedRegions) (M K m n : ℕ) : Prop where
  side_even : ∃ k : ℤ, 𝒮.side / cubeSide 𝒮 M n = 2 * (k : ℝ)
  side_ge : 2 * cubeSide 𝒮 M n ≤ 𝒮.side
  cubes_eq : ∀ e : ℕ, M = 𝒮.L ^ e → ∀ C : Set 𝒮.Point, C ∈ 𝒮.cubeGrid M n ↔
    ∃ C' ∈ PeriodicLattice.standardCubePartition 𝒮.L m (PeriodicLattice.coarseCubeIndex K e n),
      ∀ p, levelUnitsPoint 𝒮 K p ∈ C ↔ physicalTorusPoint 𝒮.L m p ∈ C'
  cover_injective : ∀ c : Fin 4 → ℝ,
    InjOn (Torus.torusProj 4 𝒮.side) {p | ∀ μ, |p μ - c μ| < cubeSide 𝒮 M n}
  sum_squares : ∀ x : 𝒮.Point,
    ∑ᶠ Q ∈ {Q : LevelCube 𝒮 M | Q.level = n}, Q.productBump x ^ 2 = 1
variable {𝒮 : RegionSequence.NestedRegions} {M : ℕ}
def LevelCube.cornerCells (Q : LevelCube 𝒮 M) : Set (Set 𝒮.Point) :=
  {C | ∃ c ∈ Torus.spacingLattice 4 𝒮.side (cubeSide 𝒮 M Q.level),
    C = Torus.cubeAt c (cubeSide 𝒮 M Q.level) ∧ IsCornerOf 𝒮 c (cubeSide 𝒮 M Q.level) Q.centre}
structure LevelCube.BumpProperties (Q : LevelCube 𝒮 M) : Prop where
  points_eq : Q.pts = ⋃₀ Q.cornerCells
  corner_count : Q.cornerCells.ncard = 2 ^ 4
  only_corner_cubes : ∀ C ∈ 𝒮.cubeGrid M Q.level, (C ∩ Q.strictPts).Nonempty → C ∈ Q.cornerCells
  smooth : ContDiff ℝ ∞ fun p => Q.productBump (Torus.torusProj 4 𝒮.side p)
  nonneg : ∀ x, 0 ≤ Q.productBump x
  le_one : ∀ x, Q.productBump x ≤ 1
  support_compact : IsCompact (tsupport Q.productBump)
  support_subset :
    tsupport Q.productBump ⊆ {x | Torus.supNorm (x - Q.centre) < 2 / 3 * cubeSide 𝒮 M Q.level}
structure TransitionCutoffs (𝒮 : RegionSequence.NestedRegions) (M n : ℕ) : Prop where
  distance_lipschitz : 𝒮.Ω n ≠ univ → ∀ x x' : 𝒮.Point,
    distToOutside 𝒮 n x ≠ ⊤ ∧
      |(distToOutside 𝒮 n x).toReal - (distToOutside 𝒮 n x').toReal| ≤
        Torus.supNorm (x - x')
  transition_eq_zero : ∀ x, distToOutside 𝒮 n x < ENNReal.ofReal (mollifyRadius 𝒮 M n) →
    levelTransition 𝒮 M n x = 0
  transition_eq_one : ∀ x, ENNReal.ofReal (2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x →
    levelTransition 𝒮 M n x = 1
  squares : ∀ x, sinCutoff 𝒮 M n x ^ 2 + cosCutoff 𝒮 M n x ^ 2 = 1
  sine_support : tsupport (sinCutoff 𝒮 M n) ⊆
    {x | ENNReal.ofReal (mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x}
  values_far : ∀ x, ENNReal.ofReal (2 * mollifyRadius 𝒮 M n) ≤ distToOutside 𝒮 n x →
    sinCutoff 𝒮 M n x = 1 ∧ cosCutoff 𝒮 M n x = 0
  cosine_support : tsupport (cosCutoff 𝒮 M n) ⊆
    {x | distToOutside 𝒮 n x ≤ ENNReal.ofReal (2 * mollifyRadius 𝒮 M n)}
structure LevelCube.SupportBounds (Q : LevelCube 𝒮 M) : Prop where
  support_subset : Q.supp ⊆
    {x | Torus.supNorm (x - Q.centre) < 2 / 3 * cubeSide 𝒮 M Q.level} ∩
      {x | Q.level ≠ 0 →
        ENNReal.ofReal (mollifyRadius 𝒮 M Q.level) ≤ distToOutside 𝒮 Q.level x} ∩
      {x | distToOutside 𝒮 (Q.level + 1) x ≤
        ENNReal.ofReal (2 * mollifyRadius 𝒮 M (Q.level + 1))}
  thickened_subset : ∀ ς : ℝ, 0 ≤ ς → ς ≤ 1 →
    Q.thicken ς ⊆ {x | Torus.supNorm (x - Q.centre) < 5 / 6 * cubeSide 𝒮 M Q.level}
structure LevelCube.CutoffProperties (Q : LevelCube 𝒮 M) : Prop where
  inner_eq_one : ∀ x ∈ Q.thicken (1 / 6), Q.smallCutoff x = 1
  inner_support : tsupport Q.smallCutoff ⊆ Q.thicken (1 / 3)
  outer_eq_one : ∀ x ∈ Q.thicken (1 / 2), Q.largeCutoff x = 1
  outer_support : tsupport Q.largeCutoff ⊆ Q.thicken (2 / 3)
  inner_mul_partition : ∀ x, Q.smallCutoff x * Q.partitionFn x = Q.partitionFn x
def LevelCube.liftedOpenCube (Q : LevelCube 𝒮 M) : Set (Fin 4 → ℝ) :=
  {p | ∀ μ, |p μ - Q.liftedCentre μ| < cubeSide 𝒮 M Q.level}
def LevelCube.localProj (Q : LevelCube 𝒮 M) (p : Fin 4 → ℝ) : Q.system.setting.Point :=
  Torus.torusProj 4 Q.system.setting.side p
structure LevelCube.FirstTypeProperties (Q : LevelCube 𝒮 M) : Prop where
  setting_eq : ∃ h : Q.IsAdmissible, Q.system.setting = Q.torusSetting h
  cover_bijective : BijOn (Torus.torusProj 4 𝒮.side) Q.liftedOpenCube Q.strictPts
  localCover_injective :
    InjOn Q.localProj (PartitionCubes.closedCube Q.liftedCentre (6 * cubeSide 𝒮 M Q.level))
  embed_cover : ∀ p ∈ Q.liftedOpenCube,
    Q.system.embed (Torus.torusProj 4 𝒮.side p) = Q.localProj p
  embed_bijective : BijOn Q.system.embed Q.strictPts (Q.localProj '' Q.liftedOpenCube)
  embed_add : ∀ p v : Fin 4 → ℝ, p ∈ Q.liftedOpenCube → p + v ∈ Q.liftedOpenCube →
    Q.system.embed (Torus.torusProj 4 𝒮.side p + Torus.torusProj 4 𝒮.side v) =
      Q.system.embed (Torus.torusProj 4 𝒮.side p) + Q.localProj v
  local_oneLength : ∀ p ∈ Q.liftedOpenCube, ∀ p' ∈ Q.liftedOpenCube,
    Torus.lOneNorm (Q.localProj p - Q.localProj p') = ∑ μ, |p μ - p' μ|
  local_supLength : ∀ p ∈ Q.liftedOpenCube, ∀ p' ∈ Q.liftedOpenCube,
    Torus.supNorm (Q.localProj p - Q.localProj p') = ‖p - p'‖
  oneLength_le : ∀ p ∈ Q.liftedOpenCube, ∀ p' ∈ Q.liftedOpenCube,
    Torus.lOneNorm (Torus.torusProj 4 𝒮.side p - Torus.torusProj 4 𝒮.side p') ≤
      ∑ μ, |p μ - p' μ|
  supLength_le : ∀ p ∈ Q.liftedOpenCube, ∀ p' ∈ Q.liftedOpenCube,
    Torus.supNorm (Torus.torusProj 4 𝒮.side p - Torus.torusProj 4 𝒮.side p') ≤ ‖p - p'‖
  embed_sites : ∀ j : ℕ, j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < 𝒮.s) →
    Q.system.embed '' ((Torus.spacingLattice 4 𝒮.side (𝒮.scale j) : Set 𝒮.Point) ∩ Q.strictPts) =
      (Torus.spacingLattice 4 Q.system.setting.side (𝒮.scale j) :
          Set Q.system.setting.Point) ∩
        Q.localProj '' Q.liftedOpenCube
  embed_cubes : ∀ j : ℕ, j ≤ Q.level ∨ (j = Q.level + 1 ∧ Q.level < 𝒮.s) →
    (fun C => Q.system.embed '' C) ''
        {C | C ∈ Torus.cubePartition 4 𝒮.side (𝒮.scale j) ∧ C ⊆ Q.strictPts} =
      {C | C ∈ Torus.cubePartition 4 Q.system.setting.side (𝒮.scale j) ∧
        C ⊆ Q.localProj '' Q.liftedOpenCube}
  upper_region_block : Torus.IsCubeUnion (cubeSide 𝒮 M Q.level) Q.nextRegion
  upper_region_next : 𝒮.L ≤ M → Torus.IsCubeUnion (𝒮.scale (Q.level + 1)) Q.nextRegion
  mem_next_iff : ∀ x ∈ Q.strictPts,
    x ∈ 𝒮.Ω (Q.level + 1) ↔ Q.system.embed x ∈ Q.system.setting.Ω (Q.level + 1)
  local_hodge : ∀ A ∈ Q.system.forms,
    curlTorusAdj (curlTorus A) + dTorus (rangeProj (dTorusAdj A)) =
      bondLap A - dTorus (complProj (dTorusAdj A))
structure LevelCube.TransfersAreAdjoint (Q : LevelCube 𝒮 M) (φ : 𝒮.Point → ℝ) : Prop where
  bonds : ∀ v ∈ Q.system.forms, ∀ A ∈ 𝒮.oneForms,
    bondInner (Q.system.pushBonds φ v) A = bondInner v (Q.system.pullBonds φ A)
  sites : ∀ (f : Q.system.setting.FineSite → ℝ) (g : 𝒮.FineSite → ℝ),
    Dirichlet.innerSum (Q.system.pushSites φ f) g = Dirichlet.innerSum f (Q.system.pullSites φ g)
  tensors : ∀ r : ℕ, r = 1 ∨ r = 2 → ∀ (J : Q.system.setting.Tensor r)
    (J' : 𝒮.Tensor r),
    tensorInner (Q.system.pushTensor φ J) J' = tensorInner J (Q.system.pullTensor φ J')
def iteratedPartial {k : ℕ} (F : (Fin 4 → ℝ) → ℝ) (ν : Fin k → Fin 4) (p : Fin 4 → ℝ) : ℝ :=
  iteratedFDeriv ℝ k F p fun i => Pi.single (ν i) 1
def liftToEuclidean (φ : 𝒮.Point → ℝ) (p : Fin 4 → ℝ) : ℝ := φ (Torus.torusProj 4 𝒮.side p)
structure LevelCube.TransferFnProperties (Q : LevelCube 𝒮 M) (φ : 𝒮.Point → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (liftToEuclidean (Q.system.transferFn φ))
  derivative_sup : ∀ (k : ℕ) (ν : Fin k → Fin 4),
    ⨆ p, |iteratedPartial (liftToEuclidean (Q.system.transferFn φ)) ν p| =
      ⨆ p, |iteratedPartial (liftToEuclidean φ) ν p|
  lipschitz : ∀ x x' : Q.system.setting.Point,
    |Q.system.transferFn φ x - Q.system.transferFn φ x'| ≤
      (⨆ μ : Fin 4, ⨆ p, |iteratedPartial (liftToEuclidean φ) (fun _ : Fin 1 => μ) p|) *
        Torus.lOneNorm (x - x')
def cubeFunctionsAndMaps : Prop :=
  BumpsExist ∧
  ∀ (𝒮 : RegionSequence.NestedRegions) (K m M R₁ : ℕ), 𝒮.IsLevelUnitChain K m M R₁ →
    (∀ n ≤ topLevel 𝒮, CubeGridAtLevel 𝒮 M K m n) ∧
    (∀ Q : LevelCube 𝒮 M, Q.BumpProperties) ∧
    (∀ n, 1 ≤ n → n ≤ 𝒮.s + 1 → TransitionCutoffs 𝒮 M n) ∧
    (∀ Q : LevelCube 𝒮 M, Q.SupportBounds) ∧
    (∀ Q ∈ active 𝒮 M, Q.CutoffProperties) ∧
    (∀ Q : LevelCube 𝒮 M, Q.IsFirstType → Q.FirstTypeProperties) ∧
    (∀ Q ∈ active 𝒮 M, ∀ φ : 𝒮.Point → ℝ, tsupport φ ⊆ Q.thicken (5 / 6) →
      Q.TransfersAreAdjoint φ) ∧
    (∀ Q : LevelCube 𝒮 M, Q.IsFirstType → ∀ φ : 𝒮.Point → ℝ, tsupport φ ⊆ Q.thicken (5 / 6) →
      ContDiff ℝ ∞ (liftToEuclidean φ) → Q.TransferFnProperties φ) ∧
    (∀ b ∈ 𝒮.bonds, ∀ y ∈ 𝒮.allCentres, AnchoredIn (𝒮.cellOf y) b →
      (b.source : 𝒮.Point) ∈ Torus.doubledSiteCube 𝒮.L 𝒮.ξ 𝒮.Ω y)
end YangMills.Construction.PartitionCubes
