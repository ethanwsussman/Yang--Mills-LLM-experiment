import YangMills.Construction.InfiniteLattice.IsometriesOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.OneLatticeAtOneSpacing
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.Lattice.ActionOfLatticeIsometries
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
namespace YangMills.Construction.InfiniteLattice
def SymmetryActionRules.Statement : Prop :=
  ∀ r r' : LatticeSymmetry 1,
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      r.actOn (r'.actOn F) = (r.comp r').actOn F) ∧
    (∀ F F' : GaugeField 1 → ℂ, IsBoundedObservable F → IsBoundedObservable F' →
      r.actOn (fun U => F U * F' U) =
        fun U => r.actOn F U * r.actOn F' U) ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      r.actOn (fun U => conj (F U)) = fun U => conj (r.actOn F U)) ∧
    (∀ p : ElementaryPlaquette 1,
      (∀ q : ElementaryPlaquette 1, q = r.plaquetteMap p ↔ q.cornerSet = r.pointMap '' p.cornerSet) ∧
      r.actOn (fun U : GaugeField 1 => faceEnergy U p) =
        fun U : GaugeField 1 => faceEnergy U (r.plaquetteMap p)) ∧
    (∀ O : Set AmbientSpace, r.actOn '' regionObservables 1 O = regionObservables 1 (r.imageSet O)) ∧
    r.actOn '' continuousLocalFunctions 1 = continuousLocalFunctions 1 ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F → IsLocalObservable F →
      observableSupport (r.actOn F) = r.linkImage (observableSupport F)) ∧
    (∃ s : LatticeSymmetry 1, s.toFun ∘ r.toFun = id ∧ r.toFun ∘ s.toFun = id) ∧
    (∃ s : LatticeSymmetry 1, s.toFun = r.toFun ∘ r'.toFun) ∧
    (r.comp r').pullbackField = r'.pullbackField ∘ r.pullbackField ∧
    (∃ h : GaugeField 1 ≃ₜ GaugeField 1, ⇑h = r.pullbackField) ∧
    ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      observableSupNorm (r.actOn F) = observableSupNorm F
end YangMills.Construction.InfiniteLattice
