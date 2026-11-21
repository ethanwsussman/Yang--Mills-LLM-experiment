import YangMills.Construction.Towers.BlocksOfATower
import YangMills.Construction.Towers.ContourFamiliesAtTheSideInfinity
import YangMills.Construction.Towers.IndexBoxesAndBlocksOfOrderZero
import YangMills.Construction.Towers.TowerDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set
open InfiniteLattice (AmbientSpace)
namespace Tower
section PeriodicSide
open PeriodicLattice (FourTorus pointOnAxis unitBlock refinedBlock contourSet bondCorridor
  crossingPath levelDepth sublattice pivot sitesIn axialPath shiftAcross)
def torusTranslation {L m : ℕ} (v : FourTorus L m) : FourTorus L m → FourTorus L m :=
  fun p => p + v
def IsSignedAxisStep {L m : ℕ} {i : ℤ} (e : PeriodicLattice.Bond L m i) (ε : ℤ) (μ : Fin 4) :
    Prop :=
  e.target - e.source = ε • PeriodicLattice.unitStep L m i μ
def HasStepsOf {L m : ℕ} {i : ℤ} (ν : Fin 4 → ℤ)
    (Γ : List (PeriodicLattice.Bond L m i)) : Prop :=
  open Classical in
  (∀ μ, (Γ.filter fun e => decide (IsSignedAxisStep e (ν μ).sign μ)).length = (ν μ).natAbs) ∧
    ∀ e ∈ Γ, ∃ μ, ν μ ≠ 0 ∧ IsSignedAxisStep e (ν μ).sign μ
structure RefinedBlocksPartition (L m k n j : ℕ) : Prop where
  eq_image : ∀ y : Vertex L m k j,
    refinedBlock n y = offsetPoint (meshAt L k (j - n)) (y : FourTorus L m) '' offsetBox L n
  injOn_offset : ∀ y : Vertex L m k j,
    InjOn (offsetPoint (meshAt L k (j - n)) (y : FourTorus L m)) (offsetBox L n)
  offsetBox_ncard : (offsetBox L n).ncard = L ^ (4 * n)
  ncard_eq : ∀ y : Vertex L m k j, (refinedBlock n y).ncard = L ^ (4 * n)
  subset_sublattice : ∀ y : Vertex L m k j,
    refinedBlock n y ⊆ (sublattice L m (levelDepth k (j - n)) : Set (FourTorus L m))
  existsUnique_mem : ∀ x : Vertex L m k (j - n),
    ∃! y : Vertex L m k j, (x : FourTorus L m) ∈ refinedBlock n y
  image_add : ∀ y v : Vertex L m k j,
    refinedBlock n (y + v) = torusTranslation (v : FourTorus L m) '' refinedBlock n y
  eq_biUnion_lower : 1 ≤ n → ∀ y : Vertex L m k j,
    refinedBlock n y =
      ⋃ x ∈ (sitesIn (unitBlock y) : Set (Vertex L m k (j - 1))), refinedBlock (n - 1) x
  pairwiseDisjoint_lower : 1 ≤ n → ∀ y : Vertex L m k j,
    (sitesIn (unitBlock y) : Set (Vertex L m k (j - 1))).PairwiseDisjoint
      fun x => refinedBlock (n - 1) x
structure FaceSteps (L m k n j : ℕ) : Prop where
  step_mem : ∀ (y : Vertex L m k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L n → ∀ μ : Fin 4,
    2 * ν μ < (L : ℤ) ^ n - 1 →
      offsetPoint (meshAt L k (j - n)) (y : FourTorus L m) ν +
        pointOnAxis L m μ (meshAt L k (j - n)) ∈ refinedBlock n y
  step_mem_next : ∀ (y : Vertex L m k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L n → ∀ μ : Fin 4,
    2 * ν μ = (L : ℤ) ^ n - 1 →
      offsetPoint (meshAt L k (j - n)) (y : FourTorus L m) ν +
          pointOnAxis L m μ (meshAt L k (j - n)) ∈
        refinedBlock n (y + PeriodicLattice.unitStep L m (levelDepth k j) μ)
  disjoint_next : ∀ (y : Vertex L m k j) (μ : Fin 4),
    Disjoint (refinedBlock n (y + PeriodicLattice.unitStep L m (levelDepth k j) μ))
      (refinedBlock n y)
structure BlockTranslateAlongBond (L m k n j : ℕ) : Prop where
  bijOn : ∀ c : Edge L m k j,
    BijOn (torusTranslation ((c.target : FourTorus L m) - (c.source : FourTorus L m)))
      (refinedBlock n c.source) (refinedBlock n c.target)
  coe_shiftAcross : ∀ (c : Edge L m k j) (x : Vertex L m k (j - n)),
    (x : FourTorus L m) ∈ refinedBlock n c.source →
      ((shiftAcross c x : Vertex L m k (j - n)) : FourTorus L m) =
        (x : FourTorus L m) + ((c.target : FourTorus L m) - (c.source : FourTorus L m))
  isAxialDisplacement : ∀ (c : Edge L m k j) (μ : Fin 4),
    c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      ∀ x : Vertex L m k (j - n), (x : FourTorus L m) ∈ refinedBlock n c.source →
        PeriodicLattice.IsAxialDisplacement x (shiftAcross c x) μ ((L : ℤ) ^ n)
  crossingPath_eq : ∀ (c : Edge L m k j) (μ : Fin 4),
    c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      ∀ x : Vertex L m k (j - n), (x : FourTorus L m) ∈ refinedBlock n c.source →
        crossingPath c x = (List.range (L ^ n)).map fun i =>
          PeriodicLattice.Bond.forwardFrom
            (x + i • PeriodicLattice.unitStep L m (levelDepth k (j - n)) μ) μ
  crossingPath_vertex_mem : ∀ c : Edge L m k j, c.IsPositivelyOriented →
    ∀ x : Vertex L m k (j - n), (x : FourTorus L m) ∈ refinedBlock n c.source →
      ∀ z : Vertex L m k (j - n),
        (z = x ∨ z = shiftAcross c x ∨ ∃ e ∈ crossingPath c x, z = e.source ∨ z = e.target) →
          (z : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target
def AxialPathMultiplicity (L m k n j : ℕ) : Prop :=
  ∀ e : Edge L m k (j - n), e.IsPositivelyOriented →
    {p : Edge L m k j × Vertex L m k (j - n) | p.1.IsPositivelyOriented ∧
      (p.2 : FourTorus L m) ∈ refinedBlock n p.1.source ∧ e ∈ crossingPath p.1 p.2}.ncard = L ^ n
structure AdjacentBlocksBounds (L m k n j : ℕ) : Prop where
  sites_near : ∀ c : Edge L m k j, c.IsPositivelyOriented →
    ∀ x ∈ refinedBlock n c.source ∪ refinedBlock n c.target, ∃ ν : Fin 4 → ℤ,
      x = offsetPoint (meshAt L k (j - n)) (c.source : FourTorus L m) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k (j - n)| < 3 / 2 * meshAt L k j
  sites_nearer : ∀ c : Edge L m k j, c.IsPositivelyOriented →
    ∀ x ∈ refinedBlock n c.source, ∃ ν : Fin 4 → ℤ,
      x = offsetPoint (meshAt L k (j - n)) (c.source : FourTorus L m) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k (j - n)| < 1 / 2 * meshAt L k j
  bonds_encard_le : ∀ c : Edge L m k j, c.IsPositivelyOriented →
    {e : Edge L m k (j - n) | e.IsPositivelyOriented ∧
      (e.source : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target ∧
      (e.target : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target}.encard ≤
        ((8 * L ^ (4 * n) : ℕ) : ℕ∞)
  encard_le_eight : ∀ e : Edge L m k (j - n),
    {c : Edge L m k j | c.IsPositivelyOriented ∧
      (e.source : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target ∧
      (e.target : FourTorus L m) ∈ refinedBlock n c.source ∪ refinedBlock n c.target}.encard ≤ 8
structure ContourTranslation (L m k n j : ℕ) : Prop where
  contours : ∀ (y : Vertex L m k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L 1 →
    ∀ x : Vertex L m k (j - 1),
      (x : FourTorus L m) = offsetPoint (meshAt L k (j - 1)) (y : FourTorus L m) ν →
        (x : FourTorus L m) ∈ unitBlock y ∧ ∀ Γ ∈ contourSet y x,
          PeriodicLattice.IsBondPathFromTo Γ (y.toSublattice (levelDepth k (j - 1))) x ∧
            HasStepsOf ν Γ ∧ Γ.length = ∑ μ, (ν μ).natAbs ∧
            ∑ μ, (ν μ).natAbs ≤ 2 * (L - 1) ∧
            ∀ z : Vertex L m k (j - 1),
              (z = y.toSublattice (levelDepth k (j - 1)) ∨ z = x ∨
                  ∃ e ∈ Γ, z = e.source ∨ z = e.target) →
                (z : FourTorus L m) ∈ unitBlock y
  isDistancePreserving : ∀ v : Vertex L m k j,
    IsDistancePreserving (torusTranslation (v : FourTorus L m))
  mapsSublatticeAndEdges : ∀ v : Vertex L m k j, ∀ i ≤ j,
    MapsSublatticeOnto k i (torusTranslation (v : FourTorus L m)) ∧
      MapsEdgesOnto k i (torusTranslation (v : FourTorus L m))
  contourSet_translate : ∀ (v y : Vertex L m k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L 1 →
    ∀ x : Vertex L m k (j - 1),
      (x : FourTorus L m) = offsetPoint (meshAt L k (j - 1)) (y : FourTorus L m) ν →
        pathImage (k := k) (j := j - 1) (torusTranslation (v : FourTorus L m)) ''
            contourSet y x =
          contourSet (y + v) (x + v.toSublattice (levelDepth k (j - 1)))
  crossingPath_translate : ∀ (v : Vertex L m k j) (c : Edge L m k j), c.IsPositivelyOriented →
    ∀ z : Vertex L m k (j - n), (z : FourTorus L m) ∈ refinedBlock n c.source →
      pathImage (k := k) (j := j - n) (torusTranslation (v : FourTorus L m)) (crossingPath c z) =
        axialPath (z + v.toSublattice (levelDepth k (j - n)))
          (shiftAcross c z + v.toSublattice (levelDepth k (j - n)))
structure PivotOnAxialPath (L m k j : ℕ) : Prop where
  length_eq : ∀ (c : Edge L m k j) (μ : Fin 4),
    c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      (axialPath (c.source.toSublattice (levelDepth k (j - 1)))
        (c.target.toSublattice (levelDepth k (j - 1)))).length = L
  existsUnique_pivot : ∀ (c : Edge L m k j) (μ : Fin 4),
    c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      ∃! e : Edge L m k (j - 1), PeriodicLattice.IsPivot c e
  pivot_source : ∀ (c : Edge L m k j) (μ : Fin 4),
    c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      ∀ e : Edge L m k (j - 1), PeriodicLattice.IsPivot c e →
        (e.source : FourTorus L m) = (c.source : FourTorus L m) +
          pointOnAxis L m μ ((((L : ℝ) - 1) / 2) * meshAt L k (j - 1))
  eq_pivot : ∀ (c : Edge L m k j) (μ : Fin 4),
    c.target - c.source = PeriodicLattice.unitStep L m (levelDepth k j) μ →
      ∀ e : Edge L m k (j - 1), PeriodicLattice.IsPivot c e → e = pivot c
end PeriodicSide
namespace FullSpace
def spaceTranslation (v : AmbientSpace) : AmbientSpace → AmbientSpace := fun p => p + v
def IsSignedAxisStep {a : ℝ} (e : InfiniteLattice.Link a) (ε : ℤ) (μ : Fin 4) : Prop :=
  e.terminal - e.initial = ε • InfiniteLattice.axisStep a μ
def HasStepsOf {a : ℝ} (ν : Fin 4 → ℤ) (Γ : List (InfiniteLattice.Link a)) : Prop :=
  open Classical in
  (∀ μ, (Γ.filter fun e => decide (IsSignedAxisStep e (ν μ).sign μ)).length = (ν μ).natAbs) ∧
    ∀ e ∈ Γ, ∃ μ, ν μ ≠ 0 ∧ IsSignedAxisStep e (ν μ).sign μ
structure RefinedCubesPartition (L k n j : ℕ) : Prop where
  eq_image : ∀ y : Vertex L k j,
    cubeOfOrder L (meshAt L k (j - n)) n y =
      offsetPoint (meshAt L k (j - n)) (y : AmbientSpace) '' offsetBox L n
  injOn_offset : ∀ y : Vertex L k j,
    InjOn (offsetPoint (meshAt L k (j - n)) (y : AmbientSpace)) (offsetBox L n)
  offsetBox_ncard : (offsetBox L n).ncard = L ^ (4 * n)
  ncard_eq : ∀ y : Vertex L k j,
    (cubeOfOrder L (meshAt L k (j - n)) n y).ncard = L ^ (4 * n)
  subset_sublattice : ∀ y : Vertex L k j,
    cubeOfOrder L (meshAt L k (j - n)) n y ⊆
      (InfiniteLattice.latticeSubgroup (meshAt L k (j - n)) : Set AmbientSpace)
  existsUnique_mem : ∀ x : Vertex L k (j - n),
    ∃! y : Vertex L k j, (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n y
  image_add : ∀ y v : Vertex L k j,
    cubeOfOrder L (meshAt L k (j - n)) n (y + v) =
      spaceTranslation (v : AmbientSpace) '' cubeOfOrder L (meshAt L k (j - n)) n y
  eq_biUnion_lower : 1 ≤ n → ∀ y : Vertex L k j,
    cubeOfOrder L (meshAt L k (j - n)) n y =
      ⋃ x ∈ cubeVertices L (meshAt L k (j - 1)) y,
        cubeOfOrder L (meshAt L k (j - n)) (n - 1) x
  pairwiseDisjoint_lower : 1 ≤ n → ∀ y : Vertex L k j,
    (cubeVertices L (meshAt L k (j - 1)) y).PairwiseDisjoint
      fun x => cubeOfOrder L (meshAt L k (j - n)) (n - 1) x
structure FaceSteps (L k n j : ℕ) : Prop where
  step_mem : ∀ (y : Vertex L k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L n → ∀ μ : Fin 4,
    2 * ν μ < (L : ℤ) ^ n - 1 →
      offsetPoint (meshAt L k (j - n)) (y : AmbientSpace) ν +
          Pi.single μ (meshAt L k (j - n)) ∈
        cubeOfOrder L (meshAt L k (j - n)) n y
  step_mem_next : ∀ (y : Vertex L k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L n → ∀ μ : Fin 4,
    2 * ν μ = (L : ℤ) ^ n - 1 →
      offsetPoint (meshAt L k (j - n)) (y : AmbientSpace) ν +
          Pi.single μ (meshAt L k (j - n)) ∈
        cubeOfOrder L (meshAt L k (j - n)) n
          (y + InfiniteLattice.axisStep (meshAt L k j) μ)
  disjoint_next : ∀ (y : Vertex L k j) (μ : Fin 4),
    Disjoint
      (cubeOfOrder L (meshAt L k (j - n)) n
        (y + InfiniteLattice.axisStep (meshAt L k j) μ))
      (cubeOfOrder L (meshAt L k (j - n)) n y)
structure CubeTranslateAlongLink (L k n j : ℕ) : Prop where
  bijOn : ∀ c : Edge L k j,
    BijOn (spaceTranslation ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace)))
      (cubeOfOrder L (meshAt L k (j - n)) n c.initial)
      (cubeOfOrder L (meshAt L k (j - n)) n c.terminal)
  coe_shifted : ∀ (c : Edge L k j) (x : Vertex L k (j - n)),
    (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
      ((shifted c x : Vertex L k (j - n)) : AmbientSpace) =
        (x : AmbientSpace) + ((c.terminal : AmbientSpace) - (c.initial : AmbientSpace))
  isAxisDisplacement : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∀ x : Vertex L k (j - n),
        (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
          IsAxisDisplacement x (shifted c x) μ ((L : ℤ) ^ n)
  crossingPath_eq : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∀ x : Vertex L k (j - n),
        (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
          crossingPath c x = (List.range (L ^ n)).map fun i =>
            InfiniteLattice.Link.forwardFrom
              (x + i • InfiniteLattice.axisStep (meshAt L k (j - n)) μ) μ
  crossingPath_vertex_mem : ∀ c : Edge L k j, c.IsPositivelyOriented →
    ∀ x : Vertex L k (j - n),
      (x : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
        ∀ z : Vertex L k (j - n),
          (z = x ∨ z = shifted c x ∨ ∃ e ∈ crossingPath c x, z = e.initial ∨ z = e.terminal) →
            (z : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
              cubeOfOrder L (meshAt L k (j - n)) n c.terminal
def AxisPathMultiplicity (L k n j : ℕ) : Prop :=
  ∀ e : Edge L k (j - n), e.IsPositivelyOriented →
    {p : Edge L k j × Vertex L k (j - n) | p.1.IsPositivelyOriented ∧
      (p.2 : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n p.1.initial ∧
      e ∈ crossingPath p.1 p.2}.ncard = L ^ n
structure AdjacentCubesBounds (L k n j : ℕ) : Prop where
  sites_near : ∀ c : Edge L k j, c.IsPositivelyOriented →
    ∀ x ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal,
      ∃ ν : Fin 4 → ℤ, x = offsetPoint (meshAt L k (j - n)) (c.initial : AmbientSpace) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k (j - n)| < 3 / 2 * meshAt L k j
  sites_nearer : ∀ c : Edge L k j, c.IsPositivelyOriented →
    ∀ x ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial,
      ∃ ν : Fin 4 → ℤ, x = offsetPoint (meshAt L k (j - n)) (c.initial : AmbientSpace) ν ∧
        ∀ ρ, |(ν ρ : ℝ) * meshAt L k (j - n)| < 1 / 2 * meshAt L k j
  bonds_encard_le : ∀ c : Edge L k j, c.IsPositivelyOriented →
    {e : Edge L k (j - n) | e.IsPositivelyOriented ∧
      (e.initial : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal ∧
      (e.terminal : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal}.encard ≤
      ((8 * L ^ (4 * n) : ℕ) : ℕ∞)
  encard_le_eight : ∀ e : Edge L k (j - n),
    {c : Edge L k j | c.IsPositivelyOriented ∧
      (e.initial : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal ∧
      (e.terminal : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial ∪
        cubeOfOrder L (meshAt L k (j - n)) n c.terminal}.encard ≤ 8
structure ContourTranslation (L k n j : ℕ) : Prop where
  contours : ∀ (y : Vertex L k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L 1 →
    ∀ x : Vertex L k (j - 1),
      (x : AmbientSpace) = offsetPoint (meshAt L k (j - 1)) (y : AmbientSpace) ν →
        (x : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y ∧ ∀ Γ ∈ contourSet L y x,
          (IsLinkPath Γ ∧ LinksJoin (y : AmbientSpace) (x : AmbientSpace) Γ) ∧
            HasStepsOf ν Γ ∧ Γ.length = ∑ μ, (ν μ).natAbs ∧
            ∑ μ, (ν μ).natAbs ≤ 2 * (L - 1) ∧
            ∀ z : Vertex L k (j - 1),
              (z = toFiner (meshAt L k (j - 1)) y ∨ z = x ∨
                  ∃ e ∈ Γ, z = e.initial ∨ z = e.terminal) →
                (z : AmbientSpace) ∈ cube L (meshAt L k (j - 1)) y
  isDistancePreserving : ∀ v : Vertex L k j,
    IsDistancePreserving (spaceTranslation (v : AmbientSpace))
  mapsSublatticeAndLinks : ∀ v : Vertex L k j, ∀ i ≤ j,
    MapsSublatticeOnto (meshAt L k i) (spaceTranslation (v : AmbientSpace)) ∧
      MapsLinksOnto (meshAt L k i) (spaceTranslation (v : AmbientSpace))
  contourSet_translate : ∀ (v y : Vertex L k j) (ν : Fin 4 → ℤ), ν ∈ offsetBox L 1 →
    ∀ x : Vertex L k (j - 1),
      (x : AmbientSpace) = offsetPoint (meshAt L k (j - 1)) (y : AmbientSpace) ν →
        pathImage (a := meshAt L k (j - 1)) (spaceTranslation (v : AmbientSpace)) ''
            contourSet L y x =
          contourSet L (y + v) (x + toFiner (meshAt L k (j - 1)) v)
  crossingPath_translate : ∀ (v : Vertex L k j) (c : Edge L k j), c.IsPositivelyOriented →
    ∀ z : Vertex L k (j - n),
      (z : AmbientSpace) ∈ cubeOfOrder L (meshAt L k (j - n)) n c.initial →
        pathImage (a := meshAt L k (j - n)) (spaceTranslation (v : AmbientSpace))
            (crossingPath c z) =
          axisPath (z + toFiner (meshAt L k (j - n)) v)
            (shifted c z + toFiner (meshAt L k (j - n)) v)
structure PivotOnAxisPath (L k j : ℕ) : Prop where
  length_eq : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      (axisPath (toFiner (meshAt L k (j - 1)) c.initial)
        (toFiner (meshAt L k (j - 1)) c.terminal)).length = L
  existsUnique_pivot : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∃! e : Edge L k (j - 1), IsPivotLink L (meshAt L k (j - 1)) c e
  pivot_initial : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∀ e : Edge L k (j - 1), IsPivotLink L (meshAt L k (j - 1)) c e →
        (e.initial : AmbientSpace) = (c.initial : AmbientSpace) +
          Pi.single μ ((((L : ℝ) - 1) / 2) * meshAt L k (j - 1))
  eq_pivotLink : ∀ (c : Edge L k j) (μ : Fin 4),
    c.terminal - c.initial = InfiniteLattice.axisStep (meshAt L k j) μ →
      ∀ e : Edge L k (j - 1), IsPivotLink L (meshAt L k (j - 1)) c e →
        e = pivotLink L (meshAt L k (j - 1)) c
end FullSpace
def BlockPathContourPivotStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n j : ℕ, 1 ≤ k → n ≤ j → j ≤ k →
    (∀ m : ℕ, 0 < m →
      RefinedBlocksPartition L m k n j ∧ FaceSteps L m k n j ∧
        BlockTranslateAlongBond L m k n j ∧ AxialPathMultiplicity L m k n j ∧
        AdjacentBlocksBounds L m k n j ∧
        (1 ≤ j → ContourTranslation L m k n j ∧ PivotOnAxialPath L m k j)) ∧
    FullSpace.RefinedCubesPartition L k n j ∧ FullSpace.FaceSteps L k n j ∧
      FullSpace.CubeTranslateAlongLink L k n j ∧ FullSpace.AxisPathMultiplicity L k n j ∧
      FullSpace.AdjacentCubesBounds L k n j ∧
      (1 ≤ j → FullSpace.ContourTranslation L k n j ∧ FullSpace.PivotOnAxisPath L k j)
end Tower
end YangMills.Construction
end
