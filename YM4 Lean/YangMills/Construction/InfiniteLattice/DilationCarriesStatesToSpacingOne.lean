import YangMills.Construction.InfiniteLattice.DilationToTheUnitLatticeAsABijection
import YangMills.Construction.InfiniteLattice.ErgodicPhases
import YangMills.Construction.InfiniteLattice.InvariantFieldOfTheUnitLattice
import YangMills.Construction.InfiniteLattice.MirrorsOfTheSixteenFamiliesAndTheClassOfReflectionPositiveStates
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open MeasureTheory Set InfiniteLattice
open LatticeConventions (NormalHyperplane conjFun)
open scoped ComplexConjugate
namespace GibbsAtFixedSpacing
variable {a : ℝ}
def BorelProb.toUnit (μ : BorelProb a) : BorelProb 1 := GaugeFieldProbability.toUnit μ
namespace ScalingToUnitSpacing
def IsScaledPair (a : ℝ) (P P' : NormalHyperplane) : Prop :=
  P'.normal = P.normal ∧ P'.level = P.level / a
def TransportsFieldsObservablesMeasures (ha : 0 < a) : Prop :=
  (∃ e : GaugeField a ≃ₜ GaugeField 1, ⇑e = gaugeFieldRescale a) ∧
  BijOn (pullToUnit (E := ℂ) ha) {f | IsBoundedObservable f} {f | IsBoundedObservable f} ∧
  (∀ f g : GaugeField a → ℂ, IsBoundedObservable f → IsBoundedObservable g →
    pullToUnit ha (f + g) = pullToUnit ha f + pullToUnit ha g ∧
    pullToUnit ha (f * g) = pullToUnit ha f * pullToUnit ha g) ∧
  (∀ (c : ℂ) (f : GaugeField a → ℂ), IsBoundedObservable f →
    pullToUnit ha (c • f) = c • pullToUnit ha f) ∧
  (∀ f : GaugeField a → ℂ, IsBoundedObservable f →
    pullToUnit ha (conjFun f) = conjFun (pullToUnit ha f) ∧
    observableSupNorm (pullToUnit ha f) = observableSupNorm f) ∧
  pullToUnit (E := ℂ) ha '' continuousFns a = continuousFns 1 ∧
  (∀ S : Set AmbientSpace,
    pullToUnit (E := ℂ) ha '' boundedMeasurableIn a S = boundedMeasurableIn 1 (inverseScaling ha '' S) ∧
    pullToUnit (E := ℂ) ha '' locallyMeasurableIn a S = locallyMeasurableIn 1 (inverseScaling ha '' S)) ∧
  (∀ (μ : BorelProb a) (f : GaugeField a → ℂ), IsBoundedObservable f →
    (BorelProb.toUnit μ).integral (pullToUnit ha f) = μ.integral f) ∧
  ∃ e : BorelProb a ≃ₜ BorelProb 1, (∀ μ, e μ = BorelProb.toUnit μ) ∧
    ∀ (μ μ₁ μ₂ : BorelProb a) (s : ℝ), 0 ≤ s → s ≤ 1 →
      μ.1 = ENNReal.ofReal s • μ₁.1 + ENNReal.ofReal (1 - s) • μ₂.1 →
      (BorelProb.toUnit μ).1 =
        ENNReal.ofReal s • (BorelProb.toUnit μ₁).1 + ENNReal.ofReal (1 - s) • (BorelProb.toUnit μ₂).1
def TransportsSymmetriesAndMirrors (ha : 0 < a) : Prop :=
  (∀ g : LatticeSymmetry a, ∃ g' : LatticeSymmetry 1, g'.toFun = conjByScaling ha g.toFun) ∧
  (∀ h : LatticeSymmetry 1, ∃ g : LatticeSymmetry a, h.toFun = conjByScaling ha g.toFun) ∧
  (∀ (g : LatticeSymmetry a) (f : GaugeField a → ℂ), IsBoundedObservable f →
    pullToUnit ha (g.actOn f) = (g.toUnit ha).actOn (pullToUnit ha f)) ∧
  (∀ v : LatticePoint a,
    conjByScaling ha (shift v).toFun = (shift (pointToUnit ha v)).toFun) ∧
  (∀ g : LatticeSymmetry a, IsLinearMap ℝ g.toFun → conjByScaling ha g.toFun = g.toFun) ∧
  (∀ P P' : NormalHyperplane, IsScaledPair a P P' →
    (P.IsLatticeMirror a ↔ P'.IsLatticeMirror 1) ∧
    inverseScaling ha '' P.carrier = P'.carrier ∧
    inverseScaling ha '' P.upperHalfSpace = P'.upperHalfSpace ∧
    inverseScaling ha '' P.lowerHalfSpace = P'.lowerHalfSpace ∧
    conjByScaling ha P.reflect = P'.reflect) ∧
  {f : AmbientSpace → AmbientSpace | ∃ g : LatticeSymmetry a, g.toFun = f} = affineHyperoctahedralMaps a
def TransportsInvarianceAndErgodicity (ha : 0 < a) : Prop :=
  ∀ μ : BorelProb a,
    (∀ g : LatticeSymmetry a, IsSymmetricUnder μ.1 g ↔ IsSymmetricUnder (BorelProb.toUnit μ).1 (g.toUnit ha)) ∧
    (IsShiftInvariant μ.1 ↔ IsShiftInvariant (BorelProb.toUnit μ).1) ∧
    (∀ (P P' : NormalHyperplane) (hP : P.IsLatticeMirror a) (hP' : P'.IsLatticeMirror 1),
      IsScaledPair a P P' →
        (IsLocallyReflectionPositive hP μ ↔ IsLocallyReflectionPositive hP' (BorelProb.toUnit μ))) ∧
    (∀ f : GaugeField a → ℂ, IsBoundedObservable f →
      (Measurable[shiftInvariantSigma a] f ↔
        Measurable[unitShiftInvariantSigma] (pullToUnit ha f))) ∧
    (IsShiftInvariant μ.1 →
      (∀ f : GaugeField a → ℂ, IsBoundedObservable f →
        pullToUnit ha (condExpShiftInvariant μ.1 f) =ᵐ[(BorelProb.toUnit μ).1]
          condExpShiftInvariant (BorelProb.toUnit μ).1 (pullToUnit ha f)) ∧
      (∀ f g : GaugeField a → ℂ, IsBoundedObservable f → IsBoundedObservable g →
        plateauPairing μ.1 f g =
          ∫ U, conj (condExpShiftInvariant (BorelProb.toUnit μ).1 (pullToUnit ha f) U) *
            condExpShiftInvariant (BorelProb.toUnit μ).1 (pullToUnit ha g) U ∂(BorelProb.toUnit μ).1) ∧
      (IsShiftErgodic μ.1 ↔ IsShiftErgodic (BorelProb.toUnit μ).1))
def TransportsGibbsMeasures (a β : ℝ) : Prop :=
  ∀ μ : BorelProb a,
    (IsGibbs β μ.1 ↔ IsGibbs β (BorelProb.toUnit μ).1) ∧
    (IsPeriodicMeasure μ.1 ↔ IsPeriodicMeasure (BorelProb.toUnit μ).1) ∧
    (IsGibbs β μ.1 → (IsPeriodicGibbs β μ.1 ↔ IsPeriodicGibbs β (BorelProb.toUnit μ).1))
def UnitSpacingTransport : Prop :=
  ∀ (a : ℝ) (ha : 0 < a),
    TransportsFieldsObservablesMeasures ha ∧
    TransportsSymmetriesAndMirrors ha ∧
    TransportsInvarianceAndErgodicity ha ∧
    (∀ β : ℝ, 0 < β → TransportsGibbsMeasures a β) ∧
    ∀ μ ∈ reflectionPositiveSet a, BorelProb.toUnit μ ∈ reflectionPositiveSet 1
end ScalingToUnitSpacing
end GibbsAtFixedSpacing
end YangMills.Construction
end
