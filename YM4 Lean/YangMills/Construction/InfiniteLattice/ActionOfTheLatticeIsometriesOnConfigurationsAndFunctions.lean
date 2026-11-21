import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction
namespace GibbsAtFixedSpacing
open InfiniteLattice
variable {a : ℝ}
def PullbackProperties (g g' : LatticeSymmetry a) : Prop :=
  (∀ (U : GaugeField a) (e : Link a), U (g.linkMap e.opposite) = (U (g.linkMap e))⁻¹) ∧
  g'.pullbackField ∘ g.pullbackField = (g.comp g').pullbackField ∧
  ∃ t : LatticeSymmetry a, t.IsInverse g ∧
    ∃ φ : GaugeField a ≃ₜ GaugeField a,
      ⇑φ = g.pullbackField ∧ ⇑φ.symm = t.pullbackField
def ObservableActionRules (g g' : LatticeSymmetry a) : Prop :=
  (∀ F F' : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable F' →
    g.actOn (F * F') = g.actOn F * g.actOn F') ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    g.actOn (fun U => conj (F U)) = fun U => conj (g.actOn F U)) ∧
  (∀ S : Set AmbientSpace,
    (fun F : GaugeField a → ℂ => g.actOn F) '' boundedMeasurableIn a S =
      boundedMeasurableIn a (g.setImage S)) ∧
  ∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    (g.comp g').actOn F = g.actOn (g'.actOn F)
def IsLinearAction (g : LatticeSymmetry a) : Prop :=
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable (g.actOn F)) ∧
  (∀ F F' : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable F' →
    g.actOn (F + F') = g.actOn F + g.actOn F') ∧
  ∀ (z : ℂ) (F : GaugeField a → ℂ), IsBoundedObservable F →
    g.actOn (z • F) = z • g.actOn F
def PreservesNormAndFunctionSpaces (g : LatticeSymmetry a) : Prop :=
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    observableSupNorm (g.actOn F) = observableSupNorm F) ∧
  (∀ S : Set AmbientSpace,
    (fun F : GaugeField a → ℂ => g.actOn F) '' locallyMeasurableIn a S =
      locallyMeasurableIn a (g.setImage S)) ∧
  (fun F : GaugeField a → ℂ => g.actOn F) '' continuousFns a =
    continuousFns a ∧
  (fun F : GaugeField a → ℂ => g.actOn F) '' continuousLocal a =
    continuousLocal a
def LatticeSymmetryActionOnFields : Prop :=
  ∀ a : ℝ, 0 < a → ∀ g g' : LatticeSymmetry a,
    PullbackProperties g g' ∧
    ObservableActionRules g g' ∧
    IsLinearAction g ∧
    PreservesNormAndFunctionSpaces g
end GibbsAtFixedSpacing
end YangMills.Construction
end
