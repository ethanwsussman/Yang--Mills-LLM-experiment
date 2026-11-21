import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
open Set YangMills.Construction.TorusMetric
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
def affineImageSegment (r : SignedFrame) (v : Fin 4 → ℝ) (s : LiftedSegment) : LiftedSegment where
  tail := r.actOnVector s.tail + v
  head := r.actOnVector s.head + v
def PreservesTorusMetrics (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  (∀ x y, torusSupNorm (σ x - σ y) = torusSupNorm (x - y)) ∧
  (∀ x y, torusL1Norm (σ x - σ y) = torusL1Norm (x - y)) ∧
  (∀ x y, torusEuclidNorm (σ x - σ y) = torusEuclidNorm (x - y)) ∧
  (∀ A B : Set (FourTorus L m), setSupDist (σ '' A) (σ '' B) = setSupDist A B) ∧
  (∀ A B : Set (FourTorus L m), setEuclidDist (σ '' A) (σ '' B) = setEuclidDist A B)
def PreservesSegmentLengths (σ : FourTorus L m ≃ FourTorus L m) : Prop :=
  ∀ (r : SignedFrame) (v : Fin 4 → ℝ), IsInducedByAffine σ r v → ∀ Γ : List LiftedSegment,
    segmentsSupport (torusSide L m) (Γ.map (affineImageSegment r v)) =
        σ '' segmentsSupport (torusSide L m) Γ ∧
      pathLength (Γ.map (affineImageSegment r v)) = pathLength Γ
def LatticeIsometriesFormFiniteGroup (L m : ℕ) (i : ℤ) : Prop :=
  (∃ H : Subgroup (Equiv.Perm (FourTorus L m)),
    (H : Set (Equiv.Perm (FourTorus L m))) = latticeIsometries L m i) ∧
    (latticeIsometries L m i).Finite
def LatticeIsometriesContainGenerators (L m : ℕ) (i : ℤ) : Prop :=
  (∀ w : Site L m i, translateBy w ∈ latticeIsometries L m i) ∧
  (∀ r : SignedFrame, SignedFrame.torusEquiv L m r ∈ latticeIsometries L m i) ∧
  (∀ P : InfiniteLattice.PeriodicMirror L m i, P.reflectEquiv ∈ latticeIsometries L m i) ∧
  ∀ (μ ν : Fin 4) (hμν : μ < ν) (s : ℤˣ) (c : ℝ),
    (InfiniteLattice.ReflectionClass.diagonal μ ν hμν s).IsAdmissibleLevel (meshSize L i) c →
      ∃ σ ∈ latticeIsometries L m i, ∀ x : Fin 4 → ℝ, σ (toFourTorus L m x) =
        toFourTorus L m
          (InfiniteLattice.hyperplaneReflect
            (InfiniteLattice.ReflectionClass.diagonal μ ν hμν s).realNormal c x)
def bondEdgeSets (L m : ℕ) (j : ℤ) : Set (Set (FourTorus L m)) :=
  range (Bond.edgeSet : Bond L m j → Set (FourTorus L m))
def plaquetteFaces (L m : ℕ) (j : ℤ) : Set (Set (FourTorus L m)) :=
  range (Plaquette.face : Plaquette L m j → Set (FourTorus L m))
def MapsCellsAndCubes (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  σ '' (sublattice L m j : Set (FourTorus L m)) = sublattice L m j ∧
  (fun S => σ '' S) '' bondEdgeSets L m j = bondEdgeSets L m j ∧
  (fun S => σ '' S) '' plaquetteFaces L m j = plaquetteFaces L m j ∧
  (∀ b : Bond L m j, ((bondImage σ b).source : FourTorus L m) = σ b.source ∧
    ((bondImage σ b).target : FourTorus L m) = σ b.target) ∧
  (-(m : ℤ) < j → ∀ b : Bond L m j, (bondImage σ b).edgeSet = σ '' b.edgeSet) ∧
  (∀ p : Plaquette L m j, (plaquetteImage σ p).face = σ '' p.face) ∧
  (∀ b b' : Bond L m j, b'.edgeSet = σ '' b.edgeSet → b'.centre = σ b.centre) ∧
  (∀ p : Plaquette L m j, (plaquetteImage σ p).barycenter = σ p.barycenter) ∧
  (∀ y y' : Site L m j, (y' : FourTorus L m) = σ y → σ '' cubeAround y = cubeAround y') ∧
  (fun Q => σ '' Q) '' standardCubePartition L m j = standardCubePartition L m j
def MapsRegions (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  (∀ X : Set (FourTorus L m), IsPartitionRegion j (σ '' X) ↔ IsPartitionRegion j X) ∧
  (∀ Q ∈ standardCubePartition L m j, ∀ Q' ∈ standardCubePartition L m j,
    (CubesMeet (σ '' Q) (σ '' Q') ↔ CubesMeet Q Q') ∧
      (CubesShareFace j (σ '' Q) (σ '' Q') ↔ CubesShareFace j Q Q')) ∧
  (∀ X X' : Set (FourTorus L m), IsPartitionRegion j X → IsPartitionRegion j X' →
    (RegionsMeet j (σ '' X) (σ '' X') ↔ RegionsMeet j X X')) ∧
  (∀ X : Set (FourTorus L m), IsPartitionRegion j X → ∀ c : List (Set (FourTorus L m)),
    (IsCubeChainIn j (σ '' X) (c.map fun Q => σ '' Q) ↔ IsCubeChainIn j X c) ∧
      (IsFaceChainIn j (σ '' X) (c.map fun Q => σ '' Q) ↔ IsFaceChainIn j X c)) ∧
  (∀ X : Set (FourTorus L m), IsPartitionRegion j X →
    σ '' complementRegion j X = complementRegion j (σ '' X) ∧
    (fun C => σ '' C) '' regionComponents j X = regionComponents j (σ '' X) ∧
    (∀ n : ℤ, σ '' layerEnlargement j X n = layerEnlargement j (σ '' X) n) ∧
    (IsPartitionBox j (σ '' X) ↔ IsPartitionBox j X) ∧
    (∀ C : Set (FourTorus L m),
      IsSmallRegionComponent j (σ '' X) (σ '' C) ↔ IsSmallRegionComponent j X C) ∧
    (∀ C : Set (FourTorus L m), IsSmallRegionComponent j X C →
      σ '' componentBox j C = componentBox j (σ '' C)) ∧
    σ '' boxClosure j X = boxClosure j (σ '' X)) ∧
  ∀ Y : Set (FourTorus L m), σ '' cubeHull j Y = cubeHull j (σ '' Y)
def LatticeIsometryGroupActionStatement : Prop :=
  ∀ (L m : ℕ) (i : ℤ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → -(m : ℤ) ≤ i →
    LatticeIsometriesFormFiniteGroup L m i ∧
    (∀ σ ∈ latticeIsometries L m i, PreservesTorusMetrics σ ∧ PreservesSegmentLengths σ) ∧
    (∀ i' : ℤ, i ≤ i' → latticeIsometries L m i ⊆ latticeIsometries L m i') ∧
    LatticeIsometriesContainGenerators L m i ∧
    ∀ σ ∈ latticeIsometries L m i, ∀ j : ℤ, i ≤ j →
      MapsCellsAndCubes σ j ∧ MapsRegions σ j
end YangMills.Construction.PeriodicLattice
