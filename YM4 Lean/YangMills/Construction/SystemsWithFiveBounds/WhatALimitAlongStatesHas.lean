import YangMills.Construction.SystemsWithFiveBounds.StatesOfTheWindowForm
import YangMills.Construction.SystemsWithFiveBounds.WhatALimitInheritsForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
open YangMills.Construction.SeparatedTuples (TupleFunctional)
open YangMills.Construction.TestSpaces (SepTupleOfCard)
open YangMills.Construction.WindowLimits (StatesApproximation LimitSymmetries)
open YangMills.Construction.LimitTheorem
structure LimitAlongStatesConditions (F : StatedSideFamily) (σ : TupleFunctional) : Prop where
  isSepFunctional : YangMills.Construction.TestSpaces.IsSepFunctional (evalOnMap σ)
  symmetries : LimitSymmetries σ
  reconstruction : ReconstructionProperties σ
  onePoint_eq : ∃ c : ℝ, ∀ X : SepTupleOfCard 1, evalOnMap σ ⟨1, X⟩ = c * ∫ x, X.1 0 x
  perBall : ∀ (N : BoundConstants), BoundsHoldAt F N → ∀ (cBar : ℝ)
    (cl r : YangMills.Construction.SeparatedTuples.SepTuple → YangMills.Construction.SeparatedTuples.SepTuple → ℝ)
    (E : LawConstants),
    PerBallBoundsAt F.M ((existentialConstantsAt F.M N cBar cl r).toConditionConstants E) σ
structure WindowLimitConditions : Prop where
  approximation : ∀ {F : StatedSideFamily} (Q : WindowStates F),
    StatesApproximation Q.toCutoffCouplingSequence Q.ρ Q.ν Q.ρ_mem
  limit_conditions : ∀ {F : StatedSideFamily} (Q : WindowStates F) {σ : TupleFunctional}, Q.HasLimit σ →
    LimitAlongStatesConditions F σ
def WindowLimitProperties : Prop := WindowLimitConditions
end YangMills.Construction.SystemsWithFiveBounds
end
