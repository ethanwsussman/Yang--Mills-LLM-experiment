import YangMills.Construction.Lattice.DirichletLaplacianUnitMesh
import YangMills.Construction.Lattice.SeparatedSequencesAndRegularPairs
import YangMills.Construction.Lattice.TwoScaleOperatorDefs
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open ScaledFun
variable {d N : ℕ}
def diagSum (s : Mesh N) : GridPoint d s := ∑ μ, s.basisStep μ
namespace Scales
variable {L j : ℕ} (S : Scales d L j N)
def fineOffset : GridPoint d S.fineMesh := ((L ^ j - 1) / 2) • diagSum S.fineMesh
def coarseOffset : GridPoint d S.unitMesh := ((L - 1) / 2) • diagSum S.unitMesh
def centeredFineCell (y : GridPoint d S.unitMesh) : Finset (GridPoint d S.fineMesh) :=
  (S.fineCell y).map (Equiv.subRight S.fineOffset).toEmbedding
def centeredCoarseCell (y' : GridPoint d S.coarseMesh) : Finset (GridPoint d S.unitMesh) :=
  (S.coarseCell y').map (Equiv.subRight S.coarseOffset).toEmbedding
def centeredFineSiteAvg : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.unitMesh where
  toFun f := ofMap fun y => ∑ x ∈ S.centeredFineCell y, fineScale L j ^ d * f x
  map_add' f g := ScaledFun.ext fun y => by
    simp only [ofMap_apply, add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := ScaledFun.ext fun y => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
def centeredFineFormAvg : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.unitMesh where
  toFun A := ofMap fun b => ∑ x ∈ S.centeredFineCell b.2, fineScale L j ^ d *
    ∑ t ∈ Finset.range (L ^ j), fineScale L j * A (b.1, x + t • S.fineMesh.basisStep b.1)
  map_add' A B := ScaledFun.ext fun b => by
    simp only [ofMap_apply, add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := ScaledFun.ext fun b => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => by ring
def centeredCoarseSiteAvg : SiteFun d S.unitMesh →ₗ[ℝ] SiteFun d S.coarseMesh where
  toFun g := ofMap fun y' => ∑ y ∈ S.centeredCoarseCell y', ((L : ℝ) ^ d)⁻¹ * g y
  map_add' f g := ScaledFun.ext fun y => by
    simp only [ofMap_apply, add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := ScaledFun.ext fun y => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
def centeredCoarseFormAvg : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.coarseMesh where
  toFun B := ofMap fun c => ∑ y ∈ S.centeredCoarseCell c.2, ((L : ℝ) ^ d)⁻¹ *
    ∑ t ∈ Finset.range L, (L : ℝ)⁻¹ * B (c.1, y + t • S.unitMesh.basisStep c.1)
  map_add' A B := ScaledFun.ext fun b => by
    simp only [ofMap_apply, add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := ScaledFun.ext fun b => by
    simp only [ofMap_apply, smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => by ring
variable (Λ' : Set (GridPoint d S.coarseMesh))
def centeredRegion : Set (GridPoint d S.unitMesh) :=
  ⋃ y' ∈ Λ', (S.centeredCoarseCell y' : Set (GridPoint d S.unitMesh))
def centeredConstrained : Submodule ℝ (SiteFun d S.fineMesh) where
  carrier := {f | (∀ y, y ∉ S.centeredRegion Λ' → S.centeredFineSiteAvg f y = 0) ∧
    ∀ y' ∈ Λ', S.centeredCoarseSiteAvg (S.centeredFineSiteAvg f) y' = 0}
  add_mem' {f g} hf hg := ⟨fun y hy => by simp [hf.1 y hy, hg.1 y hy],
    fun y' hy' => by simp [hf.2 y' hy', hg.2 y' hy']⟩
  zero_mem' := ⟨fun y _ => by simp; rfl, fun y' _ => by simp; rfl⟩
  smul_mem' c f hf := ⟨fun y hy => by simp [hf.1 y hy],
    fun y' hy' => by simp [hf.2 y' hy']⟩
def centeredQuadOp : OneForm d S.unitMesh →ₗ[ℝ] OneForm d S.unitMesh :=
  oneFormRestrict (linksAvoiding (S.centeredRegion Λ')) +
    ((L : ℝ) ^ 2)⁻¹ • (LinearMap.adjoint S.centeredCoarseFormAvg ∘ₗ
      oneFormRestrict (linksMeeting Λ') ∘ₗ S.centeredCoarseFormAvg)
def centeredGaugeProj : SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh :=
  (((S.centeredConstrained Λ').map (discreteLaplacian S.fineMesh)).starProjection :
    SiteFun d S.fineMesh →ₗ[ℝ] SiteFun d S.fineMesh)
def centeredAvgTerm (a : ℝ) : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  a • (LinearMap.adjoint S.centeredFineFormAvg ∘ₗ S.centeredQuadOp Λ' ∘ₗ
    S.centeredFineFormAvg)
def centeredTwoScaleOp (a : ℝ) : OneForm d S.fineMesh →ₗ[ℝ] OneForm d S.fineMesh :=
  LinearMap.adjoint (discreteCurl S.fineMesh) ∘ₗ discreteCurl S.fineMesh +
    discreteGrad S.fineMesh ∘ₗ S.centeredGaugeProj Λ' ∘ₗ
      LinearMap.adjoint (discreteGrad S.fineMesh) +
    S.centeredAvgTerm Λ' a
def centeredTwoScaleGreen (a : ℝ)
    (h : IsUnit (S.centeredTwoScaleOp Λ' a : Module.End ℝ (OneForm d S.fineMesh))) :
    Module.End ℝ (OneForm d S.fineMesh) :=
  ↑h.unit⁻¹
end Scales
end PeriodicLattice
namespace CubeCovering
variable {L m : ℕ}
structure CubeData (L m : ℕ) where
  scales : SeparatedSequences.ScaleData
  unitLevel_eq_top : scales.unitLevel = scales.top
  gapExp : ℕ
  seq : ℕ → Set (PeriodicLattice.FourTorus L m)
  isSeparated : SeparatedSequences.IsSeparatedSequence scales ((L : ℝ) ^ gapExp) seq
  odd : Odd L
  le_blockSize : L ≤ L ^ scales.blockExp
  eight_le_gap : 8 ≤ L ^ gapExp
namespace CubeData
variable (C : CubeData L m)
def blockSize : ℕ := L ^ C.scales.blockExp
def levelScale (n : ℕ) : ℝ := C.scales.levelMesh L n
theorem two_le_base (C : CubeData L m) : 2 ≤ L := by
  by_contra h
  have h1 : L = 0 ∨ L = 1 := by omega
  have h8 := C.eight_le_gap
  rcases h1 with rfl | rfl
  · rcases Nat.eq_zero_or_pos C.gapExp with h0 | h0
    · rw [h0] at h8; omega
    · rw [zero_pow h0.ne'] at h8; omega
  · rw [one_pow] at h8; omega
theorem blockExp_pos (C : CubeData L m) : 0 < C.scales.blockExp := by
  rcases Nat.eq_zero_or_pos C.scales.blockExp with h0 | h0
  · have h := C.le_blockSize
    have h2 := C.two_le_base
    rw [h0, pow_zero] at h
    omega
  · exact h0
def torusPeriod : ℕ := 8 * C.blockSize
theorem scalesAt (C : CubeData L m) (n : ℕ) : PeriodicLattice.Scales 4 L n C.torusPeriod where
  bounds := ⟨by omega, C.two_le_base⟩
  even_multiple := by
    obtain ⟨e, he⟩ : ∃ e, C.scales.blockExp = e + 1 := ⟨C.scales.blockExp - 1, by
      have := C.blockExp_pos
      omega⟩
    have h2 := C.two_le_base
    refine ⟨4 * L ^ e, by positivity, ?_⟩
    rw [torusPeriod, blockSize, he, pow_succ]
    ring
theorem torusPeriod_pos (C : CubeData L m) : 0 < C.torusPeriod := (C.scalesAt 0).period_pos
abbrev unitMeshOf (C : CubeData L m) : PeriodicLattice.Mesh C.torusPeriod :=
  PeriodicLattice.Mesh.one C.torusPeriod_pos
end CubeData
abbrev Space : Type := Fin 4 → ℝ
def closedCube (c : Space) (a : ℝ) : Set Space := {x | ∀ μ, |x μ - c μ| ≤ a / 2}
namespace CubeData
variable (C : CubeData L m)
def coveringMap (x : Space) : PeriodicLattice.FourTorus L m :=
  fun μ => ((PeriodicLattice.meshSize L (PeriodicLattice.levelDepth C.scales.levels C.scales.top) *
    x μ : ℝ) : AddCircle (PeriodicLattice.torusSide L m))
def LiesOver (A : Set Space) (Y : Set (PeriodicLattice.FourTorus L m)) : Prop :=
  A ⊆ C.coveringMap ⁻¹' Y
def liftedLattice (n : ℕ) : Set Space :=
  C.coveringMap ⁻¹' (PeriodicLattice.sublattice L m (PeriodicLattice.levelDepth C.scales.levels n) :
    Set (PeriodicLattice.FourTorus L m))
def IsCellCentre (n : ℕ) (c : Space) : Prop :=
  -(m : ℤ) ≤ C.scales.blockPartitionIndex n ∧
    C.coveringMap c ∈ (PeriodicLattice.sublattice L m (C.scales.blockPartitionIndex n) :
      Set (PeriodicLattice.FourTorus L m))
def cellAt (n : ℕ) (c : Space) : Set Space := closedCube c (C.blockSize * C.levelScale n)
def IsCell (n : ℕ) (D : Set Space) : Prop := ∃ c, C.IsCellCentre n c ∧ D = C.cellAt n c
end CubeData
structure Cube (C : CubeData L m) where
  level : ℕ
  level_le : level ≤ C.scales.top
  center : Space
  sideLength : ℝ
  sideLength_pos : 0 < sideLength
  isUnion_cells : ∃ F : Finset (Set Space), F.card = 2 ^ 4 ∧ (∀ D ∈ F, C.IsCell level D) ∧
    closedCube center sideLength = ⋃ D ∈ F, D
namespace Cube
variable {C : CubeData L m} (Q : Cube C)
def toSet : Set Space := closedCube Q.center Q.sideLength
def enlarge (r : ℕ) : Set Space :=
  closedCube Q.center ((2 + 2 * (r : ℝ)) * C.blockSize * C.levelScale Q.level)
def neighbourhood : Set Space := Q.enlarge 1
def IsOrigin (o : Space) : Prop :=
  C.IsCellCentre Q.level o ∧ C.cellAt Q.level o ⊆ Q.enlarge 3
abbrev Origin : Type := {o : Space // Q.IsOrigin o}
abbrev FoldedTorus (_Q : Cube C) : Type := PeriodicLattice.Torus 4 C.torusPeriod
variable {Q}
def chartAt (o : Q.Origin) (x : Space) : Q.FoldedTorus :=
  fun μ => (((x μ - o.1 μ) / C.levelScale Q.level : ℝ) : AddCircle (C.torusPeriod : ℝ))
variable (Q)
abbrev meshes : PeriodicLattice.Scales 4 L Q.level C.torusPeriod := C.scalesAt Q.level
def coarseLift : Set Space :=
  open Classical in
  if Q.level < C.scales.top then
    C.liftedLattice (Q.level + 1) ∩ Q.enlarge 2 ∩
      C.coveringMap ⁻¹' SeparatedSequences.layerSet C.scales C.seq (Q.level + 1)
  else ∅
variable {Q}
def coarseSiteSet (o : Q.Origin) : Set (PeriodicLattice.GridPoint 4 Q.meshes.coarseMesh) :=
  {y' | ∃ x ∈ Q.coarseLift, chartAt o x = (y' : Q.FoldedTorus)}
def sitesOver {s : PeriodicLattice.Mesh C.torusPeriod} (o : Q.Origin)
    (X : Set (PeriodicLattice.FourTorus L m)) : Set (PeriodicLattice.GridPoint 4 s) :=
  {z | ∃ x ∈ Q.enlarge 3, chartAt o x = (z : Q.FoldedTorus) ∧ C.coveringMap x ∈ X}
variable (Q)
def IsInterior : Prop :=
  1 ≤ Q.level ∨ (Q.level = 0 ∧ C.LiesOver (Q.enlarge 3) (C.seq 0))
def IsBoundary : Prop := Q.level = 0 ∧ ¬C.LiesOver (Q.enlarge 3) (C.seq 0)
def periodicOp (o : Q.Origin) : Module.End ℝ (PeriodicLattice.OneForm 4 Q.meshes.fineMesh) :=
  Q.meshes.centeredTwoScaleOp (coarseSiteSet o) 1
def periodicGreen (_hQ : Q.IsInterior) (o : Q.Origin) (h : IsUnit (Q.periodicOp o)) :
    Module.End ℝ (PeriodicLattice.OneForm 4 Q.meshes.fineMesh) :=
  Q.meshes.centeredTwoScaleGreen (coarseSiteSet o) 1 h
def sitesInBase (o : Q.Origin) : Set (PeriodicLattice.GridPoint 4 C.unitMeshOf) :=
  sitesOver o (C.seq 0)
def interiorLinks (o : Q.Origin) : Set (PeriodicLattice.Link 4 C.unitMeshOf) :=
  {b | PeriodicLattice.Link.source b ∈ Q.sitesInBase o ∧
    PeriodicLattice.Link.target b ∈ Q.sitesInBase o}
def meetingLinks (o : Q.Origin) : Set (PeriodicLattice.Link 4 C.unitMeshOf) :=
  PeriodicLattice.linksMeeting (Q.sitesInBase o)
def interiorPlaquettes (o : Q.Origin) : Set (DirichletLaplacian.Plaquette 4 C.unitMeshOf) :=
  {p | p.2 ∈ Q.sitesInBase o ∧
    p.2 + C.unitMeshOf.basisStep p.1.1.1 ∈ Q.sitesInBase o ∧
    p.2 + C.unitMeshOf.basisStep p.1.1.1 + C.unitMeshOf.basisStep p.1.1.2 ∈ Q.sitesInBase o ∧
    p.2 + C.unitMeshOf.basisStep p.1.1.2 ∈ Q.sitesInBase o}
structure BoundaryData (o : Q.Origin) where
  links : Set (PeriodicLattice.Link 4 C.unitMeshOf)
  plaquettes : Set (DirichletLaplacian.Plaquette 4 C.unitMeshOf)
  sites : Set (PeriodicLattice.GridPoint 4 C.unitMeshOf)
  interior_subset : Q.interiorLinks o ⊆ links
  subset_meeting : links ⊆ Q.meetingLinks o
  plaquettes_eq : plaquettes = univ ∨ plaquettes = Q.interiorPlaquettes o
  sites_eq : sites = ∅ ∨ sites = (Q.sitesInBase o)ᶜ
def boundaryGreen (_hQ : Q.IsBoundary) (o : Q.Origin) (B : Q.BoundaryData o) :
    PeriodicLattice.OneForm 4 C.unitMeshOf →ₗ[ℝ] PeriodicLattice.OneForm 4 C.unitMeshOf :=
  DirichletLaplacian.dirichletGreen B.links B.plaquettes B.sites (a := 1) one_pos
end Cube
end CubeCovering
end YangMills.Construction
