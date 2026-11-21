import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SharesAndCostsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ShareFamilies
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepCosts
def levelShareFamily (a : ℝ) (L t : ℕ) : LocalDensity := fun n y V =>
  if h : n = 0 then 0 else
    haveI : NeZero n := ⟨h⟩
    levelShare a L t Finset.univ y V
def LevelSharesFormCurvatureFamily : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y → ∀ t : ℕ,
    IsCurvatureFamily (T.stepParameters y) (weightGrowthSup T.rt T.n₁ * maxOfFirstFour T.N)
      (levelShareFamily T.coupling T.side (t + 1)) ∧
    SumInvariantUnderIsometries (T.stepParameters y) (levelShareFamily T.coupling T.side (t + 1)) ∧
    ∀ (n : ℕ) [NeZero n], T.n₀ ≤ n → ∀ V : TorusField n, IsCold T.threshold V →
      ∑ z, centered (levelShareFamily T.coupling T.side (t + 1)) n z V =
        actionAtLevel T.coupling T.side (t + 1) Finset.univ V
end YangMills.Construction.ShareFamilies
end
