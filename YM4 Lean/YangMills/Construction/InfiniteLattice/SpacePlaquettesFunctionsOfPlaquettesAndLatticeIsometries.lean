import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.CutoffLattice
import YangMills.Construction.InfiniteLattice.ObservablesAndIsometriesAtOneSpacing
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice.CutoffStructure
open CutoffLattice
variable {a : ℝ}
@[reducible] def linkTopology (a : ℝ) : TopologicalSpace (GaugeField a) :=
  ⨅ e : Link a, TopologicalSpace.induced (fun U : GaugeField a => U e) inferInstance
def IsContinuousInLinks {E : Type*} [TopologicalSpace E] (B : Set (Link a))
    (F : GaugeField a → E) : Prop :=
  ∃ g : (B → Matrices.ComplexMatrix2.specialUnitary) → E, Continuous g ∧ ∀ U, F U = g (_root_.YangMills.Construction.CutoffLattice.restrictField B U)
def IsBoundaryCycle (p : ElementaryPlaquette a) (y : Fin 4 → LatticePoint a) (e : Fin 4 → Link a) : Prop :=
  range y = p.cornerSet ∧ ∀ i, (e i).initial = y i ∧ (e i).terminal = y (i + 1)
def FieldSpaceStructure (a : ℝ) : Prop :=
  (∀ e : Link a, Xor (e ∈ positiveLinks a) (e.opposite ∈ positiveLinks a)) ∧
  (positiveLinks a).Countable ∧
  Function.Bijective (valuesOnPositive : GaugeField a → positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) ∧
  @IsHomeomorph (GaugeField a) (positiveLinks a → Matrices.ComplexMatrix2.specialUnitary) (linkTopology a) _ valuesOnPositive ∧
  linkTopology a = (inferInstance : TopologicalSpace (GaugeField a)) ∧
  (∀ B : Set (Link a), B ⊆ positiveLinks a →
    CompactSpace (B → Matrices.ComplexMatrix2.specialUnitary) ∧
    TopologicalSpace.MetrizableSpace (B → Matrices.ComplexMatrix2.specialUnitary) ∧
    borel (B → Matrices.ComplexMatrix2.specialUnitary) = MeasurableSpace.pi) ∧
  CompactSpace (GaugeField a) ∧
  TopologicalSpace.MetrizableSpace (GaugeField a) ∧
  (inferInstance : MeasurableSpace (GaugeField a)) = linkSigma (univ : Set (Link a)) ∧
  ∀ B : Set (Link a), B ⊆ positiveLinks a →
    IsHomeomorph (fun U : GaugeField a =>
      (_root_.YangMills.Construction.CutoffLattice.restrictField B U, _root_.YangMills.Construction.CutoffLattice.restrictField (positiveLinks a \ B) U)) ∧
    borel ((B → Matrices.ComplexMatrix2.specialUnitary) × ((positiveLinks a \ B : Set (Link a)) → Matrices.ComplexMatrix2.specialUnitary)) =
      (borel (B → Matrices.ComplexMatrix2.specialUnitary)).prod
        (borel ((positiveLinks a \ B : Set (Link a)) → Matrices.ComplexMatrix2.specialUnitary))
def PlaquetteGeometry (a : ℝ) : Prop :=
  Function.Injective (ElementaryPlaquette.center : ElementaryPlaquette a → AmbientSpace) ∧
  (∀ p : ElementaryPlaquette a, ∀ y ∈ p.cornerSet, ‖(y : AmbientSpace) - p.center‖ = a / 2) ∧
  ∀ S : Set AmbientSpace, Bornology.IsBounded S →
    {x : LatticePoint a | (x : AmbientSpace) ∈ S}.Finite ∧ {p : ElementaryPlaquette a | p.center ∈ S}.Finite
def FaceEnergyProperties (a : ℝ) : Prop :=
  ∀ p : ElementaryPlaquette a,
    (∀ (U : GaugeField a) (y : Fin 4 → LatticePoint a) (e : Fin 4 → Link a), IsBoundaryCycle p y e →
      (1 / 2) * (Matrices.ComplexMatrix2.fullTrace ((U (e 0) * U (e 1) * U (e 2) * U (e 3) : Matrices.ComplexMatrix2.specialUnitary) : Matrices.ComplexMatrix2)).re =
        (1 / 2) * (Matrices.ComplexMatrix2.fullTrace (faceHolonomy U p : Matrices.ComplexMatrix2)).re) ∧
    (∀ U : GaugeField a, faceEnergy U p ∈ Icc (0 : ℝ) 2) ∧
    Continuous (fun U : GaugeField a => faceEnergy U p) ∧
    IsContinuousInLinks (faceLinks p) (fun U : GaugeField a => faceEnergy U p)
def SymmetryProperties (a : ℝ) : Prop :=
  (∀ f : AmbientSpace → AmbientSpace, (∃ r : LatticeSymmetry a, r.toFun = f) ↔ f ∈ affineHyperoctahedralMaps a) ∧
  ∀ r : LatticeSymmetry a,
    Function.Bijective r.linkMap ∧
    (∀ e : Link a, r.linkMap e.opposite = (r.linkMap e).opposite) ∧
    (∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) ∧
    Function.Bijective r.plaquetteMap ∧
    (∀ p : ElementaryPlaquette a, (r.plaquetteMap p).center = r.toFun p.center) ∧
    (∀ U : GaugeField a, ∃ W : GaugeField a, (W : Link a → Matrices.ComplexMatrix2.specialUnitary) = U ∘ r.linkMap) ∧
    IsHomeomorph r.pullbackField ∧
    (∃ t : LatticeSymmetry a, t.IsInverse r ∧
      Function.LeftInverse t.pullbackField r.pullbackField ∧
      Function.RightInverse t.pullbackField r.pullbackField) ∧
    (∀ (r' : LatticeSymmetry a) (A A' : GaugeField a → ℂ), IsBoundedObservable A → IsBoundedObservable A' →
      IsBoundedObservable (r.actOn A) ∧
      observableSupNorm (r.actOn A) = observableSupNorm A ∧
      r.actOn (A * A') = r.actOn A * r.actOn A' ∧
      r.actOn (fun U => conj (A U)) = (fun U => conj (r.actOn A U)) ∧
      (r.comp r').actOn A = r.actOn (r'.actOn A)) ∧
    ∀ (S : Set AmbientSpace) (A : GaugeField a → ℂ), IsBoundedObservable A →
      (IsRegionMeasurable S A ↔ IsRegionMeasurable (r.setImage S) (r.actOn A))
def EnergyCovariance (a : ℝ) : Prop :=
  (∀ (r : LatticeSymmetry a) (p : ElementaryPlaquette a) (U : GaugeField a),
    faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p)) ∧
  ∀ f : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f →
    {p : ElementaryPlaquette a |
      (fun U : GaugeField a => faceEnergy U p • f p.center) ≠ 0}.Finite ∧
    Continuous (smearedEnergy f : GaugeField a → ℂ) ∧
    (∃ B : Set (Link a), B.Finite ∧
      IsContinuousInLinks B (smearedEnergy f : GaugeField a → ℂ)) ∧
    ∀ r : LatticeSymmetry a,
      r.actOn (smearedEnergy f : GaugeField a → ℂ) =
        smearedEnergy (r.pushforwardFun f)
def SmearedEnergyAlgebra (a : ℝ) : Prop :=
  ∀ f f' : AmbientSpace → ℂ, IsBoundedBorelCompactlySupported f → IsBoundedBorelCompactlySupported f' →
    (smearedEnergy f + smearedEnergy f' : GaugeField a → ℂ) = smearedEnergy (f + f') ∧
    (fun U : GaugeField a => conj (smearedEnergy f U)) =
      smearedEnergy (fun x => conj (f x)) ∧
    (fun U : GaugeField a => Complex.exp (smearedEnergy f U) *
      Complex.exp (smearedEnergy f' U)) =
        (fun U => Complex.exp (smearedEnergy (f + f') U)) ∧
    (fun U : GaugeField a => conj (Complex.exp (smearedEnergy f U))) =
      (fun U => Complex.exp (smearedEnergy (fun x => conj (f x)) U)) ∧
    ∀ r : LatticeSymmetry a,
      r.actOn (fun U : GaugeField a => Complex.exp (smearedEnergy f U)) =
        fun U => Complex.exp (smearedEnergy (r.pushforwardFun f) U)
def FieldSpaceAndSymmetries : Prop :=
  ∀ a : ℝ, 0 < a →
    FieldSpaceStructure a ∧ PlaquetteGeometry a ∧ FaceEnergyProperties a ∧ SymmetryProperties a ∧ EnergyCovariance a ∧
      SmearedEnergyAlgebra a
end YangMills.Construction.InfiniteLattice.CutoffStructure
