import YangMills.Construction.SeparatedSequences.ClassesFramesNormsAndKernels
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
open PeriodicLattice PeriodicLattice.DirichletOperators
namespace SeparatedClasses
namespace ClassData
variable (C : ClassData)
def meshAtIndex (i : ℤ) : ℝ := (C.L : ℝ) ^ (i - (C.t : ℤ))
abbrev partitionIdx (i : ℤ) : ℤ := (C.cutoff : ℤ) - i
abbrev partitionAt (i : ℤ) : Set (Set C.Point) :=
  PeriodicLattice.standardCubePartition C.L C.m (C.partitionIdx i)
def PartitionMeshMatches : Prop :=
  ∀ i : ℤ, i ≤ (C.m : ℤ) + (C.cutoff : ℤ) →
    -(C.m : ℤ) ≤ C.partitionIdx i ∧
      C.toLevelUnits (PeriodicLattice.meshSize C.L (C.partitionIdx i)) = C.meshAtIndex i
def CubesAreUnionsOfFiner : Prop :=
  ∀ i i' : ℤ, i ≤ i' → i' ≤ (C.m : ℤ) + (C.cutoff : ℤ) →
    ∀ Q ∈ C.partitionAt i', Q = ⋃₀ PeriodicLattice.partitionCubesIn (C.partitionIdx i) Q
def SitesInteriorToCubes : Prop :=
  ∀ i : ℕ, i ≤ C.cutoff → ∀ i' : ℤ, (i : ℤ) ≤ i' → i' ≤ (C.m : ℤ) + (C.cutoff : ℤ) →
    ∀ y : C.LatticeSite i,
      (∀ Q ∈ C.partitionAt i', (y : C.Point) ∉ frontier Q) ∧
        ∃! Q, Q ∈ C.partitionAt i' ∧ (y : C.Point) ∈ interior Q
variable (Ω : ℕ → Set C.Point)
def TorusSideEvenMultiple : Prop :=
  C.toLevelUnits (PeriodicLattice.torusSide C.L C.m) =
      2 * (C.L : ℝ) ^ ((C.m : ℤ) + (C.cutoff : ℤ) - (C.t : ℤ)) ∧
    ∃ k : ℕ, 2 * (C.L : ℝ) ^ ((C.m : ℤ) + (C.cutoff : ℤ) - (C.t : ℤ)) =
      (2 * (k : ℝ)) * ((C.blockSize : ℝ) * C.coarseMesh (C.lastNonempty Ω))
abbrev blockOfSite {n : ℕ} (y : C.LatticeSite n) : Set C.Point :=
  SeparatedSequences.siteBlock C.scales y
def LayerIsCubeUnion (n : ℕ) : Prop :=
  PeriodicLattice.IsPartitionRegion (C.partitionIdx n) (C.memberAt Ω n) ∧
  PeriodicLattice.IsPartitionRegion (C.partitionIdx n) (C.memberAt Ω (n + 1)) ∧
  PeriodicLattice.IsPartitionRegion (C.partitionIdx n) (C.layerAt Ω n) ∧
  (∀ Q ∈ C.partitionAt n,
    Q ⊆ C.layerAt Ω n ↔ Q ⊆ C.memberAt Ω n ∧ ¬Q ⊆ C.memberAt Ω (n + 1)) ∧
  PeriodicLattice.partitionCubesIn (C.partitionIdx n) (C.layerAt Ω n) =
    C.blockOfSite '' C.layerSitesAt Ω n ∧
  (∀ y ∈ C.layerSitesAt Ω n, Disjoint (interior (C.blockOfSite y)) (C.memberAt Ω (n + 1))) ∧
  (∀ y ∈ C.layerSitesAt Ω n, C.blockOfSite y ⊆ C.layerAt Ω n) ∧
  C.layerAt Ω n ⊆
    C.memberAt Ω n ∩ PeriodicLattice.complementRegion (C.partitionIdx n) (C.memberAt Ω (n + 1)) ∧
  C.layerSitesAt Ω n =
    {y : C.LatticeSite n | (y : C.Point) ∈ C.memberAt Ω n ∧ (y : C.Point) ∉ C.memberAt Ω (n + 1)}
def layerSitePts (n : ℕ) : Set C.Point :=
  (fun y : C.LatticeSite n => (y : C.Point)) '' C.layerSitesAt Ω n
def ApexBlocksTileBase : Prop :=
  (∀ n ≤ C.t, ∀ n' ≤ C.t, n ≠ n' →
    Disjoint (C.layerSitePts Ω n) (C.layerSitePts Ω n')) ∧
  (∀ y y' : C.Apex Ω, y ≠ y' → Disjoint (interior y.block) (interior y'.block)) ∧
  (⋃ y : C.Apex Ω, y.block) = Ω 0 ∧
  (∀ x : C.BareSite, (x : C.Point) ∈ Ω 0 → ∃ y : C.Apex Ω, (x : C.Point) ∈ interior y.block ∧
    ∀ y' : C.Apex Ω, (x : C.Point) ∈ y'.block → y' = y) ∧
  ∀ (y : C.Apex Ω) (n : ℕ), n ≠ y.level → Disjoint (interior y.block) (C.layerAt Ω n)
def ExpansionsAnchoredAtApexes (φ : BondFrame) : Prop :=
  (∀ c ∈ C.expansionSet Ω φ, C.rowAnchor Ω c ∈ C.layerSitesAt Ω c.1 ∧
    ∀ y : C.Apex Ω, y.point = (C.rowAnchor Ω c : C.Point) → y.mesh = C.expansionMesh c) ∧
  ∀ p : C.Point, {c | c ∈ C.expansionSet Ω φ ∧ (C.rowAnchor Ω c : C.Point) = p}.encard ≤
    ((2 * Conventions.StandingParameters.dimension : ℕ) : ℕ∞)
def ChainDistTriangle : Prop :=
  ∀ p p' p'' : C.Point, C.chainDist Ω p p'' ≤
    C.chainDist Ω p p' + C.chainDist Ω p' p''
end ClassData
def BlockStructureStatement : Prop :=
  ∀ (C : ClassData) (Ω : ℕ → Set C.Point) (φ : BondFrame), Ω ∈ C.separatedClass →
    C.PartitionMeshMatches ∧ C.CubesAreUnionsOfFiner ∧ C.SitesInteriorToCubes ∧
    C.TorusSideEvenMultiple Ω ∧ (∀ n ≤ C.t, C.LayerIsCubeUnion Ω n) ∧
    C.ApexBlocksTileBase Ω ∧ C.ExpansionsAnchoredAtApexes Ω φ ∧ C.ChainDistTriangle Ω
end SeparatedClasses
end YangMills.Construction
end
