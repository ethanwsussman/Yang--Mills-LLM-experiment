import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.BondFamiliesJoinsAndContinuousFunctionsOfFinitelyManyBonds
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfASpacingAndTheirActions
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
namespace LatticeSymmetry
variable {a : ℝ}
def ActsOnLinks (r t : LatticeSymmetry a) : Prop :=
  (∀ b : Link a, r.pointPairMap ((b.initial : AmbientSpace), (b.terminal : AmbientSpace)) =
    (((r.linkMap b).initial : AmbientSpace), ((r.linkMap b).terminal : AmbientSpace))) ∧
  (∀ b : Link a, r.linkMap b.opposite = (r.linkMap b).opposite) ∧
  (∀ b : Link a, (r.comp t).linkMap b = r.linkMap (t.linkMap b)) ∧
  Function.Bijective r.linkMap
def ActsOnFaces (r t : LatticeSymmetry a) : Prop :=
  (∀ p : ElementaryPlaquette a, ∃! q : ElementaryPlaquette a,
    q.cornerSet = r.pointMap '' p.cornerSet) ∧
  (∀ p : ElementaryPlaquette a, (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet) ∧
  (∀ p : ElementaryPlaquette a, (r.comp t).plaquetteMap p = r.plaquetteMap (t.plaquetteMap p)) ∧
  Function.Bijective r.plaquetteMap
def ActsOnFields (r t : LatticeSymmetry a) : Prop :=
  (∀ (U : GaugeField a) (b : Link a), r.pullbackField U b = U (r.linkMap b)) ∧
  t.pullbackField ∘ r.pullbackField = (r.comp t).pullbackField ∧
  ∃ s : LatticeSymmetry a, s.IsInverse r ∧
    ∃ h : GaugeField a ≃ₜ GaugeField a,
      ⇑h = r.pullbackField ∧ ⇑h.symm = s.pullbackField
def ActsOnBoundedObservables (r t : LatticeSymmetry a) : Prop :=
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable (r.actOn F)) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    r.actOn (t.actOn F) = (r.comp t).actOn F) ∧
  (∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
    r.actOn (F + G) = r.actOn F + r.actOn G) ∧
  (∀ (z : ℂ) (F : GaugeField a → ℂ), IsBoundedObservable F →
    r.actOn (z • F) = z • r.actOn F) ∧
  (∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
    r.actOn (F * G) = r.actOn F * r.actOn G) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    r.actOn (fun U => conj (F U)) = fun U => conj (r.actOn F U)) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    observableSupNorm (r.actOn F) = observableSupNorm F) ∧
  (∀ S : Set AmbientSpace,
    r.actOn '' boundedRegionObservables a S = boundedRegionObservables a (r.setImage S)) ∧
  r.actOn '' FieldsAtSpacing.continuousFiniteLinkFunctions a =
    FieldsAtSpacing.continuousFiniteLinkFunctions a
end LatticeSymmetry
def LatticeSymmetryActions : Prop :=
  ∀ a : ℝ, 0 < a → ∀ r t : LatticeSymmetry a,
    r.toFun ∈ affineHyperoctahedralMaps a → t.toFun ∈ affineHyperoctahedralMaps a →
      r.ActsOnLinks t ∧ r.ActsOnFaces t ∧ r.ActsOnFields t ∧ r.ActsOnBoundedObservables t
end InfiniteLattice
end YangMills.Construction
