import YangMills.Construction.Lattice.ActionOfIsometriesAndAlgebrasOfAGridDatum
import YangMills.Construction.Lattice.GridHalvesAndReflections
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace CellGrid
open InfiniteLattice (AmbientSpace)
variable {L : ℕ} {κ : ℤ}
namespace GridSymmetry
variable {d : CellGrid L κ}
def refl : d.GridSymmetry where
  toFun := fun x => x
  isDistPreserving := ⟨Function.bijective_id, fun _ _ => rfl⟩
  image_grid := Set.image_id _
def compose (g h : d.GridSymmetry) : d.GridSymmetry where
  toFun := g.toFun ∘ h.toFun
  isDistPreserving := ⟨g.isDistPreserving.1.comp h.isDistPreserving.1,
    fun x y => (g.isDistPreserving.2 _ _).trans (h.isDistPreserving.2 x y)⟩
  image_grid := by rw [Set.image_comp, h.image_grid, g.image_grid]
end GridSymmetry
variable (d : CellGrid L κ)
def symmetryOfMap (f : d.Space → d.Space) : d.GridSymmetry :=
  open Classical in
  if hf : BoxTorus.IsDistPreserving f ∧
      f '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
        (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space)
  then ⟨f, hf.1, hf.2⟩ else GridSymmetry.refl
def indexClass (k : Fin 4 → ℤ) : d.CellIndex := fun μ => (k μ : ZMod (d.counts μ))
def cellAt (k : d.CellIndex) : Set d.Space := d.spaceCell fun μ => ((k μ).cast : ℤ)
def MapsCubeTo (g : d.reflectionGroup) (k k' : Fin 4 → ℤ) : Prop :=
  ((g : AmbientSpace ≃ᵃ[ℝ] AmbientSpace) : AmbientSpace → AmbientSpace) '' d.cellCube k =
    d.cellCube k'
def cubeTransporter (k k' : Fin 4 → ℤ) : d.reflectionGroup :=
  @Classical.epsilon _ ⟨1⟩ fun g => d.MapsCubeTo g k k'
def MapsCellTo (f : d.Space → d.Space) (c c' : Set d.Space) : Prop :=
  f ∈ d.inducedGroupMaps ∧ f '' c = c'
def cellTransporter (c c' : Set d.Space) : d.Space → d.Space :=
  @Classical.epsilon _ ⟨fun x => x⟩ fun f => d.MapsCellTo f c c'
def IsInducedSign (f : d.Space → d.Space) (s : ℝ) : Prop :=
  ∃ g : d.reflectionGroup, d.IsInducedMap f g ∧ d.linearSign g = s
def inducedSign (f : d.Space → d.Space) : ℝ := Classical.epsilon (d.IsInducedSign f)
def fixedPlanes (μ : Fin 4) (a : ℤ) : Set d.Space :=
  BoxTorus.hyperplane d.sideLengths μ (d.faceLevel μ a) ∪
    BoxTorus.hyperplane d.sideLengths μ (d.faceLevel μ a + 1 / 2 * d.sideLengths μ)
def upperSlab (μ : Fin 4) (a : ℤ) : Set d.Space :=
  BoxTorus.slab d.sideLengths μ (d.faceLevel μ a) (d.faceLevel μ a + 1 / 2 * d.sideLengths μ)
def lowerSlab (μ : Fin 4) (a : ℤ) : Set d.Space :=
  BoxTorus.slab d.sideLengths μ (d.faceLevel μ a - 1 / 2 * d.sideLengths μ) (d.faceLevel μ a)
end CellGrid
namespace GroupAndCells
open InfiniteLattice (AmbientSpace)
variable {L : ℕ} {κ : ℤ}
def ReflectionGroupActsOnCubes (d : CellGrid L κ) : Prop :=
  (∀ g ∈ d.reflectionGroup,
    (g : AmbientSpace → AmbientSpace) ''
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) : Set AmbientSpace) =
      (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L κ) : Set AmbientSpace) ∧
    ∀ S, d.IsCellCube S → d.IsCellCube ((g : AmbientSpace → AmbientSpace) '' S)) ∧
  (∀ k k' : Fin 4 → ℤ,
    (∃! g : d.reflectionGroup, d.MapsCubeTo g k k') ∧
    d.MapsCubeTo (d.cubeTransporter k k') k k' ∧
    ∀ g : d.reflectionGroup, d.MapsCubeTo g k k' →
      d.linearSign g = (-1 : ℝ) ^ ∑ μ, (k' μ - k μ)) ∧
  ∀ v : Fin 4 → ℤ, ∃ g ∈ d.reflectionGroup,
    ∀ x : AmbientSpace, g x = x + (2 * d.cellLength) • fun μ => (v μ : ℝ)
def InducedMapsFormGroup (d : CellGrid L κ) : Prop :=
  (∀ g ∈ d.reflectionGroup, ∃ f : d.Space → d.Space, d.IsInducedMap f g ∧
    BoxTorus.IsDistPreserving f ∧
    f '' (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space) =
      (BoxTorus.gridSubgroup L κ d.sideLengths : Set d.Space)) ∧
  (∀ f ∈ d.inducedGroupMaps, (d.symmetryOfMap f).toFun = f) ∧
  (fun x => x) ∈ d.inducedGroupMaps ∧
  (∀ f ∈ d.inducedGroupMaps, ∀ f' ∈ d.inducedGroupMaps, f ∘ f' ∈ d.inducedGroupMaps) ∧
  ∀ f ∈ d.inducedGroupMaps, ∃ f' ∈ d.inducedGroupMaps,
    f ∘ f' = (fun x => x) ∧ f' ∘ f = (fun x => x)
def SpaceCellsIndexed (d : CellGrid L κ) : Prop :=
  (∀ k k' : Fin 4 → ℤ, d.spaceCell k = d.spaceCell k' ↔ d.indexClass k = d.indexClass k') ∧
  (∀ k : Fin 4 → ℤ, d.spaceCell k = d.cellAt (d.indexClass k)) ∧
  d.spaceCells = range d.cellAt ∧
  d.spaceCells.ncard = d.numCells
def SimplyTransitiveOnCells (d : CellGrid L κ) : Prop :=
  (∀ f ∈ d.inducedGroupMaps, ∀ c ∈ d.spaceCells, f '' c ∈ d.spaceCells) ∧
  ∀ c ∈ d.spaceCells, ∀ c' ∈ d.spaceCells,
    (∃! f, d.MapsCellTo f c c') ∧ d.MapsCellTo (d.cellTransporter c c') c c'
def SignDescends (d : CellGrid L κ) : Prop :=
  (∀ (g g' : d.reflectionGroup) (f : d.Space → d.Space),
    d.IsInducedMap f g → d.IsInducedMap f g' → d.linearSign g = d.linearSign g') ∧
  (∀ (g : d.reflectionGroup) (f : d.Space → d.Space),
    d.IsInducedMap f g → d.inducedSign f = d.linearSign g) ∧
  (∀ f ∈ d.inducedGroupMaps, d.inducedSign f = 1 ∨ d.inducedSign f = -1) ∧
  ∀ f ∈ d.inducedGroupMaps, ∀ f' ∈ d.inducedGroupMaps,
    d.inducedSign (f ∘ f') = d.inducedSign f * d.inducedSign f'
def FaceReflectionFixedSet (d : CellGrid L κ) (μ : Fin 4) (a : ℤ)
    (θ : d.Space → d.Space) : Prop :=
  (∃ z : ℤ, d.faceLevel μ a = PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)) ∧
  (∃ z : ℤ, d.faceLevel μ a + 1 / 2 * d.sideLengths μ =
    PeriodicLattice.meshSize L κ * ((z : ℝ) + 1 / 2)) ∧
  Function.fixedPoints θ = d.fixedPlanes μ a ∧
  d.IsLinkPlaneOfSpace (BoxTorus.hyperplane d.sideLengths μ (d.faceLevel μ a)) ∧
  d.IsLinkPlaneOfSpace
    (BoxTorus.hyperplane d.sideLengths μ (d.faceLevel μ a + 1 / 2 * d.sideLengths μ)) ∧
  {S | ∃ x ∈ (d.fixedPlanes μ a)ᶜ, S = connectedComponentIn (d.fixedPlanes μ a)ᶜ x} =
    {d.upperSlab μ a, d.lowerSlab μ a} ∧
  d.upperSlab μ a ≠ d.lowerSlab μ a ∧
  θ '' d.upperSlab μ a = d.lowerSlab μ a ∧
  θ '' d.lowerSlab μ a = d.upperSlab μ a
def FaceReflectionCells (d : CellGrid L κ) (μ : Fin 4) (a : ℤ)
    (θ : d.Space → d.Space) : Prop :=
  (∀ k : d.CellIndex,
    θ '' d.cellAt k = d.cellAt (d.reflectIndex μ (a : ZMod (d.counts μ)) k)) ∧
  (∀ k : Fin 4 → ℤ,
    interior (d.spaceCell k) = BoxTorus.image d.sideLengths (interior (d.cellCube k))) ∧
  (∀ k : Fin 4 → ℤ,
    interior (d.cellAt (d.indexClass k)) =
      BoxTorus.image d.sideLengths (interior (d.cellCube k))) ∧
  ∀ k : d.CellIndex,
    (k ∈ d.halfIndices μ (a : ZMod (d.counts μ)) → interior (d.cellAt k) ⊆ d.upperSlab μ a) ∧
    (k ∉ d.halfIndices μ (a : ZMod (d.counts μ)) → interior (d.cellAt k) ⊆ d.lowerSlab μ a)
def ObservableAction (d : CellGrid L κ) : Prop :=
  (∀ g h : d.GridSymmetry,
    h.pullback ∘ g.pullback = (g.compose h).pullback ∧
    ∀ (X : Type) (F : d.GaugeConfig → X),
      g.actOnObservables (h.actOnObservables F) = (g.compose h).actOnObservables F) ∧
  (∀ g : d.GridSymmetry,
    (∀ (α β : ℂ) (F F' : d.GaugeConfig → ℂ),
      g.actOnObservables (α • F + β • F') =
        α • g.actOnObservables F + β • g.actOnObservables F') ∧
    (∀ F F' : d.GaugeConfig → ℂ,
      g.actOnObservables (F * F') = g.actOnObservables F * g.actOnObservables F') ∧
    ∀ F : d.GaugeConfig → ℂ,
      g.actOnObservables (fun U => starRingEnd ℂ (F U)) =
        fun U => starRingEnd ℂ (g.actOnObservables F U)) ∧
  ∀ g : d.GridSymmetry, g.toFun ∈ d.inducedGroupMaps →
    ∀ c c' : d.spaceCells, c'.1 = g.toFun '' c.1 →
      g.actOnObservables '' d.cellObservables c = d.cellObservables c'
def AllHold : Prop :=
  ∀ (L : ℕ) (κ : ℤ) (d : CellGrid L κ),
    ReflectionGroupActsOnCubes d ∧ InducedMapsFormGroup d ∧ SpaceCellsIndexed d ∧
      SimplyTransitiveOnCells d ∧ SignDescends d ∧
      (∀ (μ : Fin 4) (a : ℤ) (θ : d.Space → d.Space), d.IsInducedMap θ (d.faceReflect μ a) →
        FaceReflectionFixedSet d μ a θ ∧ FaceReflectionCells d μ a θ) ∧
      ObservableAction d
end GroupAndCells
end YangMills.Construction
end
