import YangMills.Construction.InfiniteLattice.ActionOfTheLatticeIsometriesOnObservables
import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.InfiniteLattice.ObservablesOfTheUnitLatticeAndItsHalfSpaces
import YangMills.Construction.InfiniteLattice.ShiftInvariantConditioningAndPlateau
import YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
open YangMills.Construction.InfiniteLattice (GaugeField IsLocalObservable IsBoundedObservable
  IsLinearPart LatticePoint UnitLatticeSymmetry shiftInvariantSigma axisShiftInvariantSigma
  observableSupNorm hyperplaneReflect latticeSubgroup shift unitRegionObservables)
def CompMapsAndPullbacks (g g' : UnitLatticeSymmetry) : Prop :=
  (g.comp g').toFun = g.toFun ∘ g'.toFun ∧
    (g.comp g').pullbackField = g'.pullbackField ∘ g.pullbackField
def ActionRulesOn (g g' : UnitLatticeSymmetry)
    (C : (GaugeField 1 → ℂ) → Prop) : Prop :=
  ∀ F G : GaugeField 1 → ℂ, C F → C G →
    (g.comp g').actOn F = g.actOn (g'.actOn F) ∧
    (∀ h : UnitLatticeSymmetry, h.IsInverse g → h.actOn (g.actOn F) = F) ∧
    g.actOn (F + G) = g.actOn F + g.actOn G ∧
    (∀ z : ℂ, g.actOn (z • F) = z • g.actOn F) ∧
    g.actOn (F * G) = g.actOn F * g.actOn G ∧
    g.actOn (fun U => conj (F U)) = (fun U => conj (g.actOn F U)) ∧
    (Continuous F → Continuous (g.actOn F))
def BasicActionProperties (g : UnitLatticeSymmetry) : Prop :=
  Function.Surjective g.linkMap ∧ IsHomeomorph g.pullbackField ∧
    (∃ h : UnitLatticeSymmetry, h.IsInverse g) ∧
    g.actOn (1 : GaugeField 1 → ℂ) = 1
def PreservesNormAndLocality (g : UnitLatticeSymmetry) : Prop :=
  ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
    IsBoundedObservable (g.actOn F) ∧ observableSupNorm (g.actOn F) = observableSupNorm F ∧
      (IsLocalObservable F → IsLocalObservable (g.actOn F))
def MirrorReflectionProperties (P : UnitMirrorPair) : Prop :=
  P.reflect.toFun = hyperplaneReflect P.normal P.height ∧
    P.reflect.toFun ∘ P.reflect.toFun = id ∧
    P.reflect.setImage {x | P.height ≤ P.normal ⬝ᵥ x} = {x | P.normal ⬝ᵥ x ≤ P.height} ∧
    P.reflect.setImage {x | P.normal ⬝ᵥ x ≤ P.height} = {x | P.height ≤ P.normal ⬝ᵥ x} ∧
    P.normal ∈ latticeSubgroup 1 ∧ P.normal ≠ 0 ∧
    (∃ w, IsLinearPart 1 P.reflect.toFun w ∧ w P.normal = -P.normal) ∧
    ∀ (k : ℤ) (v : LatticePoint 1), (v : InfiniteLattice.AmbientSpace) = (k : ℝ) • P.normal →
      P.reflect.comp (shift (-v)) = (shift v).comp P.reflect
def PositivityFromOneHalfSpace (P : UnitMirrorPair) : Prop :=
  ∀ H ∈ P.halfSpaces, ∀ ν : Measure (GaugeField 1), IsProbabilityMeasure ν →
    (∀ F ∈ unitRegionObservables H, IsLocalObservable F →
      0 ≤ ∫ U, conj (P.reflect.actOn F U) * F U ∂ν) →
    IsReflectionPositiveAcross ν P
def SymmetryActionAndReflections : Prop :=
  (∀ g g' : UnitLatticeSymmetry, CompMapsAndPullbacks g g') ∧
  (∀ (g : UnitLatticeSymmetry) (D : Set InfiniteLattice.AmbientSpace),
    (fun F : GaugeField 1 → ℂ => g.actOn F) '' unitRegionObservables D =
      unitRegionObservables (g.setImage D)) ∧
  (∀ μ : Fin 4, shiftInvariantSigma 1 ≤ axisShiftInvariantSigma μ) ∧
  (∀ g : UnitLatticeSymmetry, BasicActionProperties g) ∧
  (∀ g : UnitLatticeSymmetry, PreservesNormAndLocality g) ∧
  (∀ g g' : UnitLatticeSymmetry, ActionRulesOn g g' IsBoundedObservable) ∧
  (∀ g g' : UnitLatticeSymmetry, ActionRulesOn g g' Measurable) ∧
  (∀ (g : UnitLatticeSymmetry) (J : GaugeField 1 → ℂ), Measurable J →
    Measurable (g.actOn J)) ∧
  (∀ P : UnitMirrorPair, MirrorReflectionProperties P) ∧
  (∀ P : UnitMirrorPair, PositivityFromOneHalfSpace P)
end YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
