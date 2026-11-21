import YangMills.Construction.InfiniteLattice.DilationCarriesStatesToSpacingOne
import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling
open YangMills.Construction.InfiniteLattice (AmbientSpace LatticePoint GaugeField LatticeSymmetry
  IsBoundedObservable IsLocalObservable regionObservables observableSupNorm shift axisStep
  IsSymmetricUnder IsShiftInvariant IsPeriodicMeasure shiftInvariantSigma unitShiftInvariantSigma
  condExpShiftInvariant plateauPairing scaledCube inverseScaling gaugeFieldRescale
  gaugeFieldUnrescale pullToUnit pointToUnit conjByScaling)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair UnitMirrorPair
  IsMirrorPlaneOf IsDiagonalDirection IsReflectionPositiveAcross basisVec)
open YangMills.Construction.ReflectionPositivity.DirectionPictures (axisReflectionGroup cubeOfRadius)
variable {a : ℝ}
def TransportsObservables (ha : 0 < a) : Prop :=
  (∃ e : GaugeField a ≃ₜ GaugeField 1,
    ⇑e = gaugeFieldRescale a ∧ ⇑e.symm = gaugeFieldUnrescale ha) ∧
  BijOn (pullToUnit (E := ℂ) ha) {F | IsBoundedObservable F} {F | IsBoundedObservable F} ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    pullToUnit ha F ∘ gaugeFieldRescale a = F) ∧
  (∀ G : GaugeField 1 → ℂ, IsBoundedObservable G →
    IsBoundedObservable (G ∘ gaugeFieldRescale a) ∧
      pullToUnit ha (G ∘ gaugeFieldRescale a) = G) ∧
  (∀ F G : GaugeField a → ℂ, IsBoundedObservable F → IsBoundedObservable G →
    pullToUnit ha (F + G) = pullToUnit ha F + pullToUnit ha G ∧
      pullToUnit ha (F * G) = pullToUnit ha F * pullToUnit ha G) ∧
  (∀ (z : ℂ) (F : GaugeField a → ℂ), IsBoundedObservable F →
    pullToUnit ha (z • F) = z • pullToUnit ha F) ∧
  (∀ F : GaugeField a → ℂ, IsBoundedObservable F →
    pullToUnit ha (fun U => conj (F U)) = (fun V => conj (pullToUnit ha F V)) ∧
      observableSupNorm (pullToUnit ha F) = observableSupNorm F ∧
      (Continuous (pullToUnit ha F) ↔ Continuous F)) ∧
  (∀ S : Set AmbientSpace,
    pullToUnit ha '' regionObservables a S = regionObservables 1 (inverseScaling ha '' S) ∧
      pullToUnit ha '' {F | F ∈ regionObservables a S ∧ IsLocalObservable F} =
        {G | G ∈ regionObservables 1 (inverseScaling ha '' S) ∧ IsLocalObservable G}) ∧
  ∀ r : ℕ+, pullToUnit ha '' regionObservables a (scaledCube a r) =
    regionObservables 1 (cubeOfRadius r)
def TransportsMeasuresAndSymmetries (ha : 0 < a) : Prop :=
  (∀ g : LatticeSymmetry a, ∃ g' : LatticeSymmetry 1, g'.toFun = conjByScaling ha g.toFun) ∧
  (∀ (ν : BorelProb a) (F : GaugeField a → ℂ), IsBoundedObservable F →
    (BorelProb.toUnit ν).integral (pullToUnit ha F) = ν.integral F) ∧
  (∀ (g : LatticeSymmetry a) (F : GaugeField a → ℂ), IsBoundedObservable F →
    pullToUnit ha (g.actOn F) = (g.toUnit ha).actOn (pullToUnit ha F)) ∧
  (∀ v : LatticePoint a,
    ((shift v).toUnit ha).toFun = (shift (pointToUnit ha v)).toFun) ∧
  (∀ g : LatticeSymmetry a, IsLinearMap ℝ g.toFun → (g.toUnit ha).toFun = g.toFun) ∧
  (∀ μ : Fin 4, ((coordinateReflect a μ).toUnit ha).toFun = (coordinateReflect 1 μ).toFun) ∧
  (∀ γ : axisReflectionGroup,
    ((axisReflectionSymmetry a γ).toUnit ha).toFun = (axisReflectionSymmetry 1 γ).toFun) ∧
  (∀ t : LatticeSymmetry 1, ∃! g : LatticeSymmetry a, g.toUnit ha = t) ∧
  ∃ e : BorelProb a ≃ₜ BorelProb 1, (∀ ν, e ν = BorelProb.toUnit ν) ∧
    ∀ (ν ν₁ ν₂ : BorelProb a) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ν.1 = ENNReal.ofReal t • ν₁.1 + ENNReal.ofReal (1 - t) • ν₂.1 →
      (BorelProb.toUnit ν).1 =
        ENNReal.ofReal t • (BorelProb.toUnit ν₁).1 + ENNReal.ofReal (1 - t) • (BorelProb.toUnit ν₂).1
def IsRescaledMirror (P : MirrorPair a) (Q : UnitMirrorPair) : Prop :=
  Q.normal = P.normal ∧ Q.height = P.height / a
def IsReflectionNonnegOn (ν : BorelProb a) (P : MirrorPair a) (H : Set AmbientSpace) : Prop :=
  ∀ F : GaugeField a → ℂ, IsLocalObservable F → F ∈ regionObservables a H →
    0 ≤ ν.integral fun U => conj (P.reflect.actOn F U) * F U
def TransportsMirrors (ha : 0 < a) : Prop :=
  (∀ (v : AmbientSpace) (h : ℝ), ((∃ μ, v = basisVec μ) ∨ IsDiagonalDirection v) →
    inverseScaling ha '' {x | v ⬝ᵥ x = h} = {x | v ⬝ᵥ x = h / a} ∧
      (IsMirrorPlaneOf a {x | v ⬝ᵥ x = h} ↔ IsMirrorPlaneOf 1 {x | v ⬝ᵥ x = h / a})) ∧
  (∀ Q : UnitMirrorPair, ∃ P : MirrorPair a, IsRescaledMirror P Q) ∧
  ∀ (P : MirrorPair a) (Q : UnitMirrorPair), IsRescaledMirror P Q →
    inverseScaling ha '' P.hyperplane = Q.hyperplane ∧
      inverseScaling ha '' P.upperHalf = Q.upperHalf ∧
      inverseScaling ha '' P.lowerHalf = Q.lowerHalf ∧
      (P.reflect.toUnit ha).toFun = Q.reflect.toFun
def TransportsStateClass (ha : 0 < a) : Prop :=
  ∀ ν : BorelProb a,
    (∀ g : LatticeSymmetry a,
      IsSymmetricUnder ν.1 g ↔ IsSymmetricUnder (BorelProb.toUnit ν).1 (g.toUnit ha)) ∧
    (IsShiftInvariant ν.1 ↔ IsShiftInvariant (BorelProb.toUnit ν).1) ∧
    (IsPeriodicMeasure ν.1 ↔ IsPeriodicMeasure (BorelProb.toUnit ν).1) ∧
    (∀ (P : MirrorPair a) (Q : UnitMirrorPair), IsRescaledMirror P Q →
      (IsReflectionNonnegOn ν P P.upperHalf ↔
        IsReflectionNonnegOn (BorelProb.toUnit ν) Q Q.upperHalf) ∧
      (IsReflectionNonnegOn ν P P.lowerHalf ↔
        IsReflectionNonnegOn (BorelProb.toUnit ν) Q Q.lowerHalf) ∧
      (IsReflectionPositiveAcross ν.1 P ↔ IsReflectionPositiveAcross (BorelProb.toUnit ν).1 Q)) ∧
    (ν ∈ reflectionPositiveSet a ↔ BorelProb.toUnit ν ∈ reflectionPositiveSet 1)
def TransportsInvariantSets (ha : 0 < a) : Prop :=
  (∀ I : Set (GaugeField a), MeasurableSet I →
    (MeasurableSet[shiftInvariantSigma a] I ↔
      MeasurableSet[unitShiftInvariantSigma] (gaugeFieldRescale a '' I))) ∧
  (∀ J : Set (GaugeField 1), MeasurableSet[unitShiftInvariantSigma] J →
    ∃ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I ∧
      gaugeFieldRescale a '' I = J) ∧
  (∀ (μ : Fin 4) (I : Set (GaugeField a)), MeasurableSet I →
    ((shift (axisStep a μ)).actOn (I.indicator (1 : GaugeField a → ℂ)) =
        I.indicator 1 ↔
      (shift (axisStep 1 μ)).actOn
          ((gaugeFieldRescale a '' I).indicator (1 : GaugeField 1 → ℂ)) =
        (gaugeFieldRescale a '' I).indicator 1)) ∧
  ∀ ν : BorelProb a,
    (∀ X : Set (GaugeField a), MeasurableSet X →
      (BorelProb.toUnit ν).1 (gaugeFieldRescale a '' X) = ν.1 X) ∧
    (IsErgodicState ν ↔ IsErgodicState (BorelProb.toUnit ν)) ∧
    (IsShiftInvariant ν.1 → ∀ A B : GaugeField a → ℂ, IsBoundedObservable A →
      IsBoundedObservable B →
      pullToUnit ha (condExpShiftInvariant ν.1 A) =ᵐ[(BorelProb.toUnit ν).1]
        condExpShiftInvariant (BorelProb.toUnit ν).1 (pullToUnit ha A) ∧
      plateauPairing ν.1 A B =
        plateauPairing (BorelProb.toUnit ν).1 (pullToUnit ha A) (pullToUnit ha B))
def UnitScalingDictionary : Prop :=
  ∀ (a : ℝ) (ha : 0 < a),
    TransportsObservables ha ∧ TransportsMeasuresAndSymmetries ha ∧ TransportsMirrors ha ∧
      TransportsStateClass ha ∧ TransportsInvariantSets ha
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling
