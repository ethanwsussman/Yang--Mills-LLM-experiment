import YangMills.Construction.InfiniteLattice.ConfigurationsFunctionsAndMeasures
import YangMills.Construction.InfiniteLattice.ObservablesOnTheClosedSideOfAMirrorAndStates
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter YangMills.Construction.GibbsAtFixedSpacing
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
variable {a : ℝ}
theorem positiveLinks_eq_self (a : ℝ) :
    positiveLinks a = positiveLinkSet a :=
  Set.ext fun _ => mem_positiveLinks_iff.symm
def realContinuous (a : ℝ) : Set (GaugeField a → ℂ) :=
  {F | F ∈ continuousFns a ∧ ∀ U, (F U).im = 0}
def IsSupNormDenseIn (D C : Set (GaugeField a → ℂ)) : Prop :=
  D ⊆ C ∧ ∀ F ∈ C, ∀ ε : ℝ, 0 < ε → ∃ H ∈ D, observableSupNorm (F - H) < ε
def IsSupportedIn (F : GaugeField a → ℂ) (S : Set AmbientSpace) : Prop :=
  LinksLieIn (observableSupport F) S
def weakBasicNhd (ν : Measure (GaugeField a)) {k : ℕ} (F : Fin k → GaugeField a → ℂ)
    (ε : ℝ) : Set (Measure (GaugeField a)) :=
  {ρ | IsLatticeState ρ ∧ ∀ l, ‖stateEval ρ (F l) - stateEval ν (F l)‖ < ε}
def IsWeakBasicNhd (ν : Measure (GaugeField a))
    (N : Set (Measure (GaugeField a))) : Prop :=
  ∃ (k : ℕ) (F : Fin k → GaugeField a → ℂ) (ε : ℝ),
    1 ≤ k ∧ (∀ l, F l ∈ continuousFns a) ∧ 0 < ε ∧ N = weakBasicNhd ν F ε
def IsStateFamily (S : Set (Measure (GaugeField a))) : Prop := ∀ ρ ∈ S, IsLatticeState ρ
def asProbabilityMeasures (S : Set (Measure (GaugeField a))) :
    Set (ProbabilityMeasure (GaugeField a)) :=
  {ν | (ν : Measure (GaugeField a)) ∈ S}
def IsWeakOpen (S : Set (Measure (GaugeField a))) : Prop :=
  IsStateFamily S ∧ IsOpen[probabilityMeasuresWeakTopology a] (asProbabilityMeasures S)
def IsWeakClosed (S : Set (Measure (GaugeField a))) : Prop :=
  IsStateFamily S ∧ IsClosed[probabilityMeasuresWeakTopology a] (asProbabilityMeasures S)
def IsWeakCompact (S : Set (Measure (GaugeField a))) : Prop :=
  IsStateFamily S ∧
    @IsCompact (ProbabilityMeasure (GaugeField a)) (probabilityMeasuresWeakTopology a)
      (asProbabilityMeasures S)
def IsWeakClosedWithin (T S : Set (Measure (GaugeField a))) : Prop :=
  IsStateFamily T ∧ ∃ C, IsWeakClosed C ∧ S = T ∩ C
def StatesTendstoWeakly (ν : ℕ → Measure (GaugeField a)) (ν₀ : Measure (GaugeField a)) :
    Prop :=
  ∀ F : GaugeField a → ℂ, Continuous F →
    Tendsto (fun i => stateEval (ν i) F) atTop (𝓝 (stateEval ν₀ F))
def IsWeakClusterPoint (ν : ℕ → Measure (GaugeField a))
    (ν₀ : Measure (GaugeField a)) : Prop :=
  ∀ C : Set (GaugeField a → ℂ), C.Finite → (∀ F ∈ C, Continuous F) →
    ∀ ε : ℝ, 0 < ε → ∀ i₀ : ℕ, 1 ≤ i₀ →
      ∃ i, i₀ ≤ i ∧ ∀ F ∈ C, ‖stateEval (ν i) F - stateEval ν₀ F‖ ≤ ε
end InfiniteLattice
end YangMills.Construction
