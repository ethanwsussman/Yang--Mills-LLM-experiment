import YangMills.Construction.Geometry.TorusCovering
import YangMills.Construction.Torus.LiftsAndInducedMaps
import YangMills.Construction.VolumeTransfer.FunctionsOfFinitelyManyBondVariables
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.VolumeTransfer
open InfiniteLattice (AmbientSpace refinedLattice refinedSpacing RefinedGaugeField)
structure LatticeGeometry (L K : ℕ) where
  Point : Type
  [addCommGroup : AddCommGroup Point]
  proj : AmbientSpace →+ Point
  sites : AddSubgroup Point
  Link : Type
  src : Link → Point
  tgt : Link → Point
  flip : Link → Link
  src_flip : ∀ e, src (flip e) = tgt e
  tgt_flip : ∀ e, tgt (flip e) = src e
  link_ext : ∀ e e', src e = src e' → tgt e = tgt e' → e = e'
  Face : Type
  vertices : Face → Set Point
  center : Face → Point
  Field : Type
  [fieldTopology : TopologicalSpace Field]
  [fieldMeasurableSpace : MeasurableSpace Field]
  linkValue : Field → Link → Matrices.ComplexMatrix2.specialUnitary
  linkValue_flip : ∀ A e, linkValue A (flip e) = (linkValue A e)⁻¹
  linkValue_injective : ∀ A A', (∀ e, linkValue A e = linkValue A' e) → A = A'
  ofLinkValues : ∀ W : Link → Matrices.ComplexMatrix2.specialUnitary,
    (∀ e, W (flip e) = (W e)⁻¹) → Field
  linkValue_ofLinkValues : ∀ W hW e, linkValue (ofLinkValues W hW) e = W e
  holonomy : Field → Face → Matrices.ComplexMatrix2
  energy : Field → Face → ℝ
attribute [instance] LatticeGeometry.addCommGroup LatticeGeometry.fieldTopology
  LatticeGeometry.fieldMeasurableSpace
namespace LatticeGeometry
theorem coe_inv_specialUnitary (g : Matrices.ComplexMatrix2.specialUnitary) :
    ((g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      (g : Matrices.ComplexMatrix2)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  exact show ((g * g⁻¹ : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) = 1 from by
    rw [mul_inv_cancel]
    rfl
@[reducible] def euclidean (L K : ℕ) : LatticeGeometry L K where
  Point := AmbientSpace
  proj := AddMonoidHom.id AmbientSpace
  sites := refinedLattice L K
  Link := InfiniteLattice.Link (refinedSpacing L K)
  src e := e.initial
  tgt e := e.terminal
  flip := InfiniteLattice.Link.opposite
  src_flip _ := rfl
  tgt_flip _ := rfl
  link_ext _ _ h h' := InfiniteLattice.Link.ext (Subtype.ext h) (Subtype.ext h')
  Face := InfiniteLattice.ElementaryPlaquette (refinedSpacing L K)
  vertices p := Subtype.val '' TorusLifts.plaquetteVertexSet p
  center := InfiniteLattice.ElementaryPlaquette.center
  Field := RefinedGaugeField L K
  linkValue := refinedLinkValue L K
  linkValue_flip A e := A.2 e
  linkValue_injective _ _ h := Subtype.ext (funext h)
  ofLinkValues W hW := ⟨W, hW⟩
  linkValue_ofLinkValues _ _ _ := rfl
  holonomy A p := InfiniteLattice.faceHolonomy A.1 p
  energy A p := InfiniteLattice.faceEnergy A.1 p
@[reducible] def periodic (L m K : ℕ) : LatticeGeometry L K where
  Point := PeriodicLattice.FourTorus L m
  proj := TorusCovering.torusProjHom (PeriodicLattice.torusSide L m)
  sites := PeriodicLattice.sublattice L m (K : ℤ)
  Link := PeriodicLattice.Bond L m (K : ℤ)
  src e := e.source
  tgt e := e.target
  flip := PeriodicLattice.Bond.opposite
  src_flip _ := rfl
  tgt_flip _ := rfl
  link_ext _ _ h h' := PeriodicLattice.Bond.ext (Subtype.ext h) (Subtype.ext h')
  Face := PeriodicLattice.Plaquette L m (K : ℤ)
  vertices p := Subtype.val '' p.vertices
  center := PeriodicLattice.Plaquette.barycenter
  Field := PeriodicLattice.CompactGaugeField L m (K : ℤ)
  linkValue := periodicLinkValue L m K
  linkValue_flip A e := by
    apply Subtype.ext
    rw [coe_inv_specialUnitary]
    exact A.2.2 e (mem_univ e)
  linkValue_injective A A' h := by
    apply Subtype.ext
    funext e
    exact congrArg Subtype.val (h e)
  ofLinkValues W hW := ⟨fun e => (W e : Matrices.ComplexMatrix2), fun e _ => (W e).2, fun e _ => by
    change ((W e.opposite : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2) =
      ((W e : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)⁻¹
    rw [hW e, coe_inv_specialUnitary]⟩
  linkValue_ofLinkValues _ _ _ := rfl
  holonomy A p := PeriodicLattice.plaquetteHolonomy A.1 p
  energy A p := PeriodicLattice.plaquetteCost A.1 p
variable {L K : ℕ} (Y : LatticeGeometry L K)
def IsInducedBy (r : Y.Point → Y.Point) (g : AmbientSpace → AmbientSpace) : Prop :=
  ∀ x, r (Y.proj x) = Y.proj (g x)
def diagSign (ε : Fin 4 → ℤˣ) : Equiv.Perm AmbientSpace := TorusLifts.signedCoordinateEquiv 1 ε
theorem diagSign_apply (ε : Fin 4 → ℤˣ) (x : AmbientSpace) (μ : Fin 4) :
    diagSign ε x μ = (((ε μ : ℤˣ) : ℤ) : ℝ) * x μ :=
  rfl
def IsReflectionTranslation (r : Y.Point → Y.Point) : Prop :=
  ∃ (ε : Fin 4 → ℤˣ), ∃ t ∈ refinedLattice L K, Y.IsInducedBy r fun x => diagSign ε x + t
def MapsLinks (r : Y.Point → Y.Point) : Prop :=
  ∀ e, ∃ e', Y.src e' = r (Y.src e) ∧ Y.tgt e' = r (Y.tgt e)
variable {Y} {r : Y.Point → Y.Point}
def imageLink (hr : Y.MapsLinks r) (e : Y.Link) : Y.Link := (hr e).choose
theorem src_imageLink (hr : Y.MapsLinks r) (e : Y.Link) :
    Y.src (imageLink hr e) = r (Y.src e) :=
  (hr e).choose_spec.1
theorem tgt_imageLink (hr : Y.MapsLinks r) (e : Y.Link) :
    Y.tgt (imageLink hr e) = r (Y.tgt e) :=
  (hr e).choose_spec.2
theorem imageLink_flip (hr : Y.MapsLinks r) (e : Y.Link) :
    imageLink hr (Y.flip e) = Y.flip (imageLink hr e) :=
  Y.link_ext _ _
    (by rw [src_imageLink, Y.src_flip, Y.src_flip, tgt_imageLink])
    (by rw [tgt_imageLink, Y.tgt_flip, Y.tgt_flip, src_imageLink])
def pullback (hr : Y.MapsLinks r) (A : Y.Field) : Y.Field :=
  Y.ofLinkValues (fun e => Y.linkValue A (imageLink hr e)) fun e => by
    rw [imageLink_flip, Y.linkValue_flip]
theorem linkValue_pullback (hr : Y.MapsLinks r) (A : Y.Field) (e : Y.Link) :
    Y.linkValue (pullback hr A) e = Y.linkValue A (imageLink hr e) :=
  Y.linkValue_ofLinkValues _ _ e
def precompose (hr : Y.MapsLinks r) (F : Y.Field → ℂ) : Y.Field → ℂ :=
  F ∘ pullback hr
end LatticeGeometry
def IsInvariantUnderLinkMap {L K : ℕ} (ν : Measure (RefinedGaugeField L K))
    [IsProbabilityMeasure ν] {r : AmbientSpace → AmbientSpace}
    (hr : (LatticeGeometry.euclidean L K).MapsLinks r) : Prop :=
  ∀ F : RefinedGaugeField L K → ℂ,
    IsBoundedBorelInFinitelyManyLinks (refinedLinkValue L K) F →
      ∫ A, LatticeGeometry.precompose hr F A ∂ν = ∫ A, F A ∂ν
end YangMills.Construction.VolumeTransfer
end
