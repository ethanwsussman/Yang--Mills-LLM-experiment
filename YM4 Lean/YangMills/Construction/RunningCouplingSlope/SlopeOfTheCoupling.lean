import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open TorusLumps RenormalizationStepParameters StepReturn CouplingFlow
namespace RunningCouplingSlope
def FlowStaysAboveFloor (ℓ : StepParameters) (β : ℝ) (j : ℕ) : Prop :=
  ∀ k < j, ℓ.y₁ ≤ (couplingFlow ℓ β k).1
structure CouplingDropBetween (ℓ : StepParameters) (β c₀ c₅ C : ℝ) (i j : ℕ) : Prop where
  lower_le : 3 / 4 * c₀ * ((j : ℝ) - i) - c₅ ≤ (couplingFlow ℓ β i).1 - (couplingFlow ℓ β j).1
  le_upper : (couplingFlow ℓ β i).1 - (couplingFlow ℓ β j).1 ≤ 5 / 4 * c₀ * ((j : ℝ) - i) + c₅
  abs_sub_le : |(couplingFlow ℓ β i).1 - (couplingFlow ℓ β j).1 - ((j : ℝ) - i) * c₀| ≤
    c₅ + C * ∑ l ∈ Finset.Ico i j, (couplingFlow ℓ β l).1 ^ (-(1 / 4) : ℝ)
def HasCouplingDrop (ℓ : StepParameters) (c₀ c₅ C X : ℝ) : Prop :=
  ∀ (β : ℝ) (i j : ℕ), ℓ.y₁ ≤ β → i ≤ j → FlowStaysAboveFloor ℓ β i →
    (∀ l, i ≤ l → l < j → X ≤ (couplingFlow ℓ β l).1) → CouplingDropBetween ℓ β c₀ c₅ C i j
def slopeThreshold (X Ce c₀ : ℝ) : ℝ := max X ((4 * Ce / c₀) ^ 4)
def CouplingHasSlope : Prop :=
  ∃ cH : ℝ → ℕ → ℝ, (∀ a L, 0 ≤ cH a L) ∧ ∃ rt₀ : ChainParameters → ℝ, (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.Admissible → T.rt ≤ rt₀ T.toChainParameters → ∃ Ce ys : ℝ, 0 < Ce ∧
      ∀ y : ℝ, T.floorMin ≤ y →
      ExpansionReturnsAt (T.stepParameters y) →
      (∀ β : ℝ, y ≤ β → HasExpansion (T.stepParameters y) 0 β (wilsonWeight β)) →
      HasCouplingDrop (T.stepParameters y) (slopeConst T.side) (2 * cH T.coupling T.side) Ce
        (slopeThreshold (max y ys) Ce (slopeConst T.side))
end RunningCouplingSlope
end YangMills.Construction
end
