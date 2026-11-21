import YangMills.Construction.InfiniteLattice.StatesFunctionsAndTheWeakTopologyOfOneLattice
import YangMills.Construction.InfiniteLattice.StatesThatHaveAGivenMirror
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder NNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
namespace MirrorDomination
abbrev gibbsClassOf (β : ℝ) (Q : AddSubgroup AmbientSpace) : Set (Measure (GaugeField 1)) :=
  subgroupInvariantGibbsClass one_pos β (Q.addSubgroupOf (latticeSubgroup 1))
def EvenClassCompactNonempty (β : ℝ) : Prop :=
  Convex ℝ≥0 (gibbsClassOf β evenLattice) ∧
    IsWeakCompact (gibbsClassOf β evenLattice) ∧
    (gibbsClassOf β evenLattice).Nonempty
def MirrorStatesCompact (β : ℝ) (P : NormalLevelPair 1) : Prop :=
  Convex ℝ≥0 (mirrorReflectionPositiveStates β P) ∧
    IsWeakClosedWithin (gibbsClassOf β evenLattice) (mirrorReflectionPositiveStates β P) ∧
    IsWeakCompact (mirrorReflectionPositiveStates β P)
def ClassInclusions (β : ℝ) (P : NormalLevelPair 1) : Prop :=
  ∀ h : ℤ, Even h → 2 ≤ h →
    gibbsClassOf β evenLattice ⊆ gibbsClassOf β (axialPeriodLattice P.normal h) ∧
    gibbsClassOf β (axialPeriodLattice P.normal h) ⊆
      gibbsClassOf β (normalPeriodLattice P.normal h) ∧
    gibbsClassOf β (normalPeriodLattice P.normal h) ⊆ periodicGibbsClass one_pos β ∧
    periodicGibbsClass one_pos β = gibbsClassOf β evenLattice
def Dominates (β : ℝ) (P : NormalLevelPair 1) : Prop :=
  ∀ ν ∈ gibbsClassOf β evenLattice, ∀ A ∈ continuousLocalFunctions 1,
    (∀ U, (A U).im = 0) →
      ∃ ν₀ ∈ mirrorReflectionPositiveStates β P, stateEval ν A ≤ stateEval ν₀ A
def Statement : Prop :=
  ∀ β : ℝ, 0 < β → ∀ P : NormalLevelPair 1,
    EvenClassCompactNonempty β ∧ MirrorStatesCompact β P ∧
      ClassInclusions β P ∧ Dominates β P ∧ (mirrorReflectionPositiveStates β P).Nonempty
end MirrorDomination
end YangMills.Construction.InfiniteLattice
