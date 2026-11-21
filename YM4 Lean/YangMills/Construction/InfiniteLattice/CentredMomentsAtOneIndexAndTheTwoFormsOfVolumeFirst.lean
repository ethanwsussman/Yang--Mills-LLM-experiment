import YangMills.Construction.InfiniteLattice.LimitsAlongTheCutoffs
import Mathlib
set_option autoImplicit false
open Filter MeasureTheory
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
def IsVolumeFirstLimitOf (T : ParameterChoice.DerivedConstants) (a : ParameterChoice.FullChoice)
    (s : PeriodicLattice.ActivityDomainKind) (ρ : CutoffRemainders a) (g : ℝ)
    (S : (n : ℕ) → (Fin n → AmbientSpace → ℝ) → ℂ) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
    (ν : ∀ i, Measure (GaugeField (PeriodicLattice.meshSize a.L (((K i : ℕ)) : ℤ)))) : Prop :=
  SchwingerFunctions.IsContinuumSchwingerFamily S ∧
    ∃ (hK : Tendsto (fun i => (K i : ℕ)) atTop atTop)
      (hβ : ∀ i, β i ∈ FlowConstants.flowFirstPassageWindow T a (K i) s (ρ (K i)) g)
      (hν : ∀ i, IsInfiniteVolumeLimit a.L (K i) (β i) (ν i)),
      (VolumeFirstApproximants.mk K hK β hβ ν hν :
        VolumeFirstApproximants T a s ρ g).ConvergesTo S
end InfiniteLattice
namespace CutoffLimits.CenteredMomentsAndVolumeFirst
def centeredProduct {a : ℝ} (ν : Measure (InfiniteLattice.GaugeField a)) {k : ℕ}
    (f : Fin k → InfiniteLattice.AmbientSpace → ℝ) (U : InfiniteLattice.GaugeField a) : ℂ :=
  ∏ i, (((InfiniteLattice.smearedEnergy (f i) U : ℝ) : ℂ) -
    Probability.complexExpectation ν fun V => ((InfiniteLattice.smearedEnergy (f i) V : ℝ) : ℂ))
theorem centeredMoment_eq_expectation {a : ℝ} (ν' ν : Measure (InfiniteLattice.GaugeField a)) {k : ℕ}
    (f : Fin k → InfiniteLattice.AmbientSpace → ℝ) :
    CutoffLimits.centredMoment ν' ν f = Probability.complexExpectation ν' (centeredProduct ν f) :=
  rfl
def CenteredMomentWellDefinedReal {a : ℝ} (ν' ν : Measure (InfiniteLattice.GaugeField a)) {k : ℕ}
    (f : Fin k → InfiniteLattice.AmbientSpace → ℝ) : Prop :=
  (∀ i, Probability.IsBoundedRealRV
      (InfiniteLattice.smearedEnergy (f i) : InfiniteLattice.GaugeField a → ℝ)) ∧
    Probability.IsBoundedComplexRV (centeredProduct ν f) ∧
    (CutoffLimits.centredMoment ν' ν f).im = 0
def CenteredMomentProperties {a : ℝ} (ν' ν : Measure (InfiniteLattice.GaugeField a)) : Prop :=
  ∀ (k : ℕ) (f : Fin k → InfiniteLattice.AmbientSpace → ℝ),
    (∀ i, f i ∈ InfiniteLattice.compactTestFunctions) →
    CenteredMomentWellDefinedReal ν' ν f ∧
    (k = 0 → CutoffLimits.centredMoment ν' ν f = 1) ∧
    (∀ ς : Equiv.Perm (Fin k),
      CutoffLimits.centredMoment ν' ν (fun i => f (ς i)) = CutoffLimits.centredMoment ν' ν f) ∧
    (∀ (i : Fin k) (u v : InfiniteLattice.AmbientSpace → ℝ),
      u ∈ InfiniteLattice.compactTestFunctions → v ∈ InfiniteLattice.compactTestFunctions →
      ∀ t t' : ℝ, CutoffLimits.centredMoment ν' ν (Function.update f i (t • u + t' • v)) =
        (t : ℂ) * CutoffLimits.centredMoment ν' ν (Function.update f i u) +
          (t' : ℂ) * CutoffLimits.centredMoment ν' ν (Function.update f i v)) ∧
    CutoffLimits.centredMoment ν ν f = InfiniteLattice.centeredMoment ν f
def ExtendsFamily {D : Setting} (S : RealFamily D)
    (S' : (n : ℕ) → (Fin n → InfiniteLattice.AmbientSpace → ℝ) → ℂ) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (X : D.SepTuples n), S' n X.1 = ((S n hn X : ℝ) : ℂ)
def IsConnectedFamily {D : Setting} (S : RealFamily D) : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n),
      AmbientPoints.IsTupleSymmetric (S n hn) ∧ AmbientPoints.IsTupleMultilinear (S n hn)) ∧
    ∃ T : AmbientPoints.ConnectedFamily D.euclideanParams .euclidean, T.fn = S
def Statement : Prop :=
  (∀ (D : FixedSpacing.Setup) (ν ν' : Measure D.Fields),
    IsProbabilityMeasure ν → IsProbabilityMeasure ν' → CenteredMomentProperties ν' ν) ∧
  (∀ (s : Conventions.StandingParameters) (X : AmbientPoints.FunctionTuple s .euclidean),
    X ∈ AmbientPoints.allSeparatedTuples s .euclidean →
      ∀ i, X.2 i ∈ InfiniteLattice.compactTestFunctions) ∧
  (∀ (D : Setting) (Q : PassageSequence D) (J : Set ℕ+) (e : ℕ+ → ℕ+), StrictMono e →
    ∀ (hJ : Set.range e = J) (ν : ∀ j : J, Measure (Q.Fields j)),
    (∀ j : J, ν j ∈ Q.torusLimits j) →
    ∀ (S : RealFamily D) (S' : (n : ℕ) → (Fin n → InfiniteLattice.AmbientSpace → ℝ) → ℂ),
    ExtendsFamily S S' →
    (CutoffLimits.IsVolumeFirstLimitWith Q S J ν ↔
      InfiniteLattice.IsVolumeFirstLimitOf D.constants D.choice D.activityKind D.remainders D.g S'
        (fun i => Q.K (e i)) (fun i => Q.β (e i))
        (fun i => ν ⟨e i, hJ ▸ Set.mem_range_self i⟩)) ∧
    (CutoffLimits.IsVolumeFirstLimitWith Q S J ν → IsConnectedFamily S))
end CutoffLimits.CenteredMomentsAndVolumeFirst
end YangMills.Construction
end
