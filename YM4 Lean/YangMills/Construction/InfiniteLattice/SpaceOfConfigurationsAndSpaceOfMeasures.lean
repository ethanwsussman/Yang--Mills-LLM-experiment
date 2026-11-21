import YangMills.Construction.InfiniteLattice.BondFamiliesJoinsAndContinuousFunctionsOfFinitelyManyBonds
import Mathlib
set_option autoImplicit false
open YangMills.Construction.InfiniteLattice YangMills.Construction.GibbsAtFixedSpacing
noncomputable section
namespace YangMills.Construction.FieldsAtSpacing
def GaugeFieldsCompactProduct (a : ℝ) : Prop :=
  (∀ ℓ : Link a,
    Xor (ℓ ∈ positiveLinkSet a) (ℓ.opposite ∈ positiveLinkSet a)) ∧
  (positiveLinkSet a).Countable ∧
  Function.Bijective (linkRestriction (a := a) (positiveLinkSet a)) ∧
  IsHomeomorph (linkRestriction (a := a) (positiveLinkSet a)) ∧
  CompactSpace (GaugeField a) ∧
  TopologicalSpace.MetrizableSpace (GaugeField a) ∧
  CompactSpace (LinkVariables ↥(positiveLinkSet a)) ∧
  TopologicalSpace.MetrizableSpace (LinkVariables ↥(positiveLinkSet a))
def ContinuousFiniteLinkFunctionsDense (a : ℝ) : Prop :=
  (∃ A : Subalgebra ℂ (GaugeField a → ℂ),
    (A : Set (GaugeField a → ℂ)) = continuousFiniteLinkFunctions a ∧
      A ≤ continuousSubalgebra a) ∧
  (∀ z : ℂ, (fun _ : GaugeField a => z) ∈ continuousFiniteLinkFunctions a) ∧
  (∀ F ∈ continuousFiniteLinkFunctions a,
    (fun U => (starRingEnd ℂ) (F U)) ∈ continuousFiniteLinkFunctions a) ∧
  (∀ U V : GaugeField a, U ≠ V →
    ∃ F ∈ continuousFiniteLinkFunctions a, F U ≠ F V) ∧
  (∀ F ∈ continuousSubalgebra a, ∀ ε : ℝ, 0 < ε →
    ∃ G ∈ continuousFiniteLinkFunctions a, observableSupNorm (F - G) < ε)
def CompactFieldsAndMeasures : Prop :=
  ∀ a : ℝ, 0 < a →
    GaugeFieldsCompactProduct a ∧
    ContinuousFiniteLinkFunctionsDense a ∧
    (CompactSpace (BorelProb a) ∧ TopologicalSpace.MetrizableSpace (BorelProb a)) ∧
    ∀ μ ν : BorelProb a,
      (∀ F ∈ continuousFiniteLinkFunctions a, μ.integral F = ν.integral F) → μ = ν
end YangMills.Construction.FieldsAtSpacing
