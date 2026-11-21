import YangMills.Construction.InfiniteLattice.DilationToSpacingOne
import YangMills.Construction.InfiniteLattice.LatticeMirrorsAsHyperplanesAndToriOfAnyShape
import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder NNReal Topology
noncomputable section
namespace YangMills.Construction
open InfiniteLattice NormalFamilies UnitSpacing
namespace UnitSpacing
variable {a : ℝ}
def RescaleLatticeAndFields (ha : 0 < a) : Prop :=
  Function.Surjective (pointRescale ha) ∧
    Function.Bijective (rescaledLink ha) ∧
    rescaledLink ha '' positiveLinks a = positiveLinks 1 ∧
    Function.Bijective (rescaledPlaquette ha) ∧
    (∀ p : ElementaryPlaquette a, (rescaledPlaquette ha p).linkSet = rescaledLink ha '' p.linkSet) ∧
    (∃ e : GaugeField a ≃ₜ GaugeField 1, ⇑e = fieldRescale ha) ∧
    (∀ (U : GaugeField a) (b : Link a), fieldRescale ha U (rescaledLink ha b) = U b) ∧
    (∀ (U : GaugeField a) (p : ElementaryPlaquette a),
      faceHolonomy (fieldRescale ha U) (rescaledPlaquette ha p) =
        faceHolonomy U p) ∧
    ∀ p : ElementaryPlaquette a,
      (fun U : GaugeField 1 => faceEnergy U (rescaledPlaquette ha p)) ∘
          fieldRescale ha =
        fun U : GaugeField a => faceEnergy U p
def RescaleObservables (ha : 0 < a) : Prop :=
  BijOn (precompRescale ha) {F | IsBoundedObservable F} {F | IsBoundedObservable F} ∧
    (∀ F G : GaugeField 1 → ℂ, IsBoundedObservable F → IsBoundedObservable G →
      precompRescale ha (F + G) = precompRescale ha F + precompRescale ha G ∧
        precompRescale ha (F * G) = precompRescale ha F * precompRescale ha G) ∧
    (∀ (z : ℂ) (F : GaugeField 1 → ℂ), IsBoundedObservable F →
      precompRescale ha (z • F) = z • precompRescale ha F) ∧
    (∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
      precompRescale ha (fun U => conj (F U)) = fun U => conj (precompRescale ha F U)) ∧
    precompRescale ha '' GibbsAtFixedSpacing.continuousFns 1 =
      GibbsAtFixedSpacing.continuousFns a ∧
    (∀ S : Set AmbientSpace,
      precompRescale ha '' regionObservables 1 (scaleByInvImage a S) = regionObservables a S) ∧
    precompRescale ha '' continuousLocalFunctions 1 = continuousLocalFunctions a
def RescaleSymmetries (ha : 0 < a) : Prop :=
  (∀ r : LatticeSymmetry a, ∃ r' : LatticeSymmetry 1,
    r'.toFun = conjugateByScaling a r.toFun ∧
      ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
        r.actOn (precompRescale ha F) = precompRescale ha (r'.actOn F)) ∧
    (∀ r' : LatticeSymmetry 1, ∃ r : LatticeSymmetry a,
      r'.toFun = conjugateByScaling a r.toFun) ∧
    (∀ v : LatticePoint a,
      conjugateByScaling a (shift v).toFun = (shift (pointRescale ha v)).toFun) ∧
    ∀ w ∈ hyperoctahedralLinearGroup, conjugateByScaling a w = w
def RescaleMirrors (ha : 0 < a) : Prop :=
  (∀ n ∈ normalSet, ∀ c : ℝ, IsAllowedLevel a n c ↔ IsAllowedLevel 1 n (c / a)) ∧
    ∀ (P : NormalLevelPair a) (P' : NormalLevelPair 1), P'.normal = P.normal →
      P'.level = P.level / a →
      conjugateByScaling a (reflectAcross P.normal P.level) =
          reflectAcross P'.normal P'.level ∧
        (∀ ε : ℤˣ,
          scaleByInvImage a (closedHalfSpace P.normal P.level ε) =
              closedHalfSpace P'.normal P'.level ε ∧
            precompRescale ha '' halfSpaceObservables 1 P'.normal P'.level ε =
              halfSpaceObservables a P.normal P.level ε) ∧
        ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
          P.conjReflectObservable (precompRescale ha F) =
            precompRescale ha (P'.conjReflectObservable F)
def KernelScaleFree (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ (W : LinkWindow a) (F : GaugeField 1 → ℂ), IsBoundedObservable F →
    W.conditionalExpectation ha β (precompRescale ha F) =
      (rescaledWindow ha W).conditionalExpectation one_pos β F ∘ fieldRescale ha
def RescaleStates (ha : 0 < a) : Prop :=
  (∀ ν : Measure (GaugeField a), IsLatticeState ν →
    IsLatticeState (dilatedState ha ν) ∧
      ∀ F : GaugeField 1 → ℂ, IsBoundedObservable F →
        stateEval (dilatedState ha ν) F = stateEval ν (precompRescale ha F)) ∧
    BijOn (dilatedState ha) {ν | IsLatticeState ν} {ν | IsLatticeState ν} ∧
    (∀ ν₁ ν₂ : Measure (GaugeField a), IsLatticeState ν₁ → IsLatticeState ν₂ →
      ∀ t : ℝ≥0, t ≤ 1 →
      dilatedState ha (t • ν₁ + (1 - t) • ν₂) =
        t • dilatedState ha ν₁ + (1 - t) • dilatedState ha ν₂) ∧
    (∃ e : ProbabilityMeasure (GaugeField a) ≃ ProbabilityMeasure (GaugeField 1),
      (∀ ν, ((e ν : ProbabilityMeasure (GaugeField 1)) : Measure (GaugeField 1)) =
        dilatedState ha (ν : Measure (GaugeField a))) ∧
      Continuous[probabilityMeasuresWeakTopology a, probabilityMeasuresWeakTopology 1] e ∧
      Continuous[probabilityMeasuresWeakTopology 1, probabilityMeasuresWeakTopology a] e.symm) ∧
    ∀ (ν : Measure (GaugeField a)) (μs : ℕ → Measure (GaugeField a)), IsLatticeState ν →
      (∀ i, 1 ≤ i → IsLatticeState (μs i)) →
      (IsWeakClusterPoint μs ν ↔
        IsWeakClusterPoint (fun i => dilatedState ha (μs i)) (dilatedState ha ν))
def RescaleInvarianceAndPositivity (ha : 0 < a) : Prop :=
  ∀ ν : Measure (GaugeField a), IsLatticeState ν →
    (∀ (r : LatticeSymmetry a) (r' : LatticeSymmetry 1),
      r'.toFun = conjugateByScaling a r.toFun →
        (IsSymmetricUnder ν r ↔ IsSymmetricUnder (dilatedState ha ν) r')) ∧
      ∀ (P : NormalLevelPair a) (P' : NormalLevelPair 1), P'.normal = P.normal →
        P'.level = P.level / a → ∀ ε : ℤˣ,
        (∀ G ∈ halfSpaceObservables a P.normal P.level ε,
            0 ≤ stateEval ν (P.conjReflectObservable G * G)) ↔
          ∀ F ∈ halfSpaceObservables 1 P'.normal P'.level ε,
            0 ≤ stateEval (dilatedState ha ν) (P'.conjReflectObservable F * F)
def RescaleGibbsClasses (ha : 0 < a) (β : ℝ) : Prop :=
  ∀ ν : Measure (GaugeField a), IsLatticeState ν →
    (ν ∈ gibbsClass ha β ↔ dilatedState ha ν ∈ gibbsClass (a := 1) one_pos β) ∧
      (∀ Q : AddSubgroup (LatticePoint a),
        ν ∈ subgroupInvariantGibbsClass ha β Q ↔
          dilatedState ha ν ∈ subgroupInvariantGibbsClass one_pos β (subgroupRescale ha Q)) ∧
      (ν ∈ periodicGibbsClass ha β ↔
        dilatedState ha ν ∈ periodicGibbsClass (a := 1) one_pos β)
def periodNorms (Γ : PeriodSublattice a) : Set ℝ :=
  {s | ∃ γ ∈ Γ.periods, γ ≠ 0 ∧ s = ‖(γ : AmbientSpace)‖}
def RescalePeriodSublattices (ha : 0 < a) (β : ℝ) : Prop :=
  (∀ Γ : AddSubgroup (LatticePoint a),
    (∃ P : PeriodSublattice a, P.periods = Γ) ↔
      ∃ P' : PeriodSublattice 1, P'.periods = subgroupRescale ha Γ) ∧
    ∀ (P : PeriodSublattice a) (P' : PeriodSublattice 1),
      P'.periods = subgroupRescale ha P.periods →
      IsLatticeState (P.liftedGibbsMeasure β) ∧
        dilatedState ha (P.liftedGibbsMeasure β) = P'.liftedGibbsMeasure β ∧
        IsLeast (periodNorms P) P.minNonzeroNorm ∧
        IsLeast (periodNorms P') P'.minNonzeroNorm ∧
        P'.minNonzeroNorm = a⁻¹ * P.minNonzeroNorm
def TransportToUnitSpacing : Prop :=
  ∀ (a β : ℝ) (ha : 0 < a), 0 < β →
    RescaleLatticeAndFields ha ∧
      RescaleObservables ha ∧
      RescaleSymmetries ha ∧
      RescaleMirrors ha ∧
      KernelScaleFree ha β ∧
      RescaleStates ha ∧
      RescaleInvarianceAndPositivity ha ∧
      RescaleGibbsClasses ha β ∧
      RescalePeriodSublattices ha β
end UnitSpacing
end YangMills.Construction
