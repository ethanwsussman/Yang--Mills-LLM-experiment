import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.JointLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps TorusFields WeightedResponses
def flowCoupling (ℓ : StepParameters) (β : ℝ) (j : ℕ) : ℝ := (couplingFlow ℓ β j).1
def flowFunctional (ℓ : StepParameters) (β : ℝ) (j : ℕ) : TorusFunctional := (couplingFlow ℓ β j).2
def IsColdCoupling (ℓ : StepParameters) (t : ℕ) (D : TorusFunctional) (x : ℝ) : Prop :=
  ∃ f : LocalDensity, ColdExpansion ℓ t x D f
def wilsonPartition (β : ℝ) (m : ℕ) [NeZero m] : ℝ := ∫ W, wilsonWeight β m W ∂(fieldHaar m)
def IsBoundedMeasurable {X : Type} [MeasurableSpace X] (F : X → ℝ) : Prop :=
  Measurable F ∧ ∃ C : ℝ, ∀ u, |F u| ≤ C
structure IsChainDensity (ℓ : StepParameters) (β : ℝ) (x : ℕ → ℝ) (t n : ℕ) [NeZero n]
    (D : TorusFunctional) : Prop where
  isProbability : IsProbabilityMeasure (chainJointLaw ℓ β x t n)
  initial_integral : ∀ G : TorusField (fineSide ℓ.side t n) → ℝ, IsBoundedMeasurable G →
    ∫ u, G (initialField ℓ t n u) ∂(chainJointLaw ℓ β x t n) =
      (∫ W, G W * wilsonWeight β (fineSide ℓ.side t n) W ∂(fieldHaar (fineSide ℓ.side t n))) /
        wilsonPartition β (fineSide ℓ.side t n)
  integral_eq : ∫ V, D n V ∂(fieldHaar n) = wilsonPartition β (fineSide ℓ.side t n)
  partition_pos : 0 < wilsonPartition β (fineSide ℓ.side t n)
  final_integral : ∀ F : TorusField n → ℝ, IsBoundedMeasurable F →
    ∫ u, F (finalField ℓ t n u) ∂(chainJointLaw ℓ β x t n) =
      (∫ V, F V * D n V ∂(fieldHaar n)) / ∫ V, D n V ∂(fieldHaar n)
def FlowIsChainLawAt (ℓ : StepParameters) (β : ℝ) : Prop :=
  ∀ (t n : ℕ) [NeZero n], IsChainDensity ℓ β (flowCoupling ℓ β) t n (flowFunctional ℓ β t) ∧
    (1 ≤ t → (∀ V : TorusField n, 0 < flowFunctional ℓ β t n V) ∧
      ∀ A : Set (TorusField n), MeasurableSet A → 0 < fieldHaar n A →
        0 < (chainJointLaw ℓ β (flowCoupling ℓ β) t n) (finalField ℓ t n ⁻¹' A))
def FlowHasExpansionAt (ℓ : StepParameters) (β : ℝ) : Prop :=
  ∀ t : ℕ,
    ((∀ j < t, ℓ.y₁ ≤ flowCoupling ℓ β j) → HasExpansion ℓ t (flowCoupling ℓ β t) (flowFunctional ℓ β t)) ∧
    ((∀ j ≤ t, ℓ.y₁ ≤ flowCoupling ℓ β j) → |flowCoupling ℓ β (t + 1) - flowCoupling ℓ β t| ≤ 2 * ℓ.B)
def FlowReadOffAt (ℓ : StepParameters) (β : ℝ) : Prop :=
  ∀ t : ℕ, (∀ j ≤ t, ℓ.y₁ ≤ flowCoupling ℓ β j) → ∀ x : ℝ,
    IsColdCoupling ℓ (t + 1) (flowFunctional ℓ β (t + 1)) x ↔ x = flowCoupling ℓ β (t + 1)
def FlowUniqueAt (ℓ : StepParameters) (β : ℝ) : Prop :=
  ∀ (x : ℕ → ℝ) (t : ℕ), x 0 = β → (∀ j < t, ℓ.y₁ ≤ x j) →
    (∀ j < t, IsColdCoupling ℓ (j + 1) (chainFunctional ℓ β x (j + 1)) (x (j + 1))) →
    ∀ j ≤ t, x j = flowCoupling ℓ β j ∧ chainFunctional ℓ β x j = flowFunctional ℓ β j
end YangMills.Construction.ClusterExpansionOfAStep
end
