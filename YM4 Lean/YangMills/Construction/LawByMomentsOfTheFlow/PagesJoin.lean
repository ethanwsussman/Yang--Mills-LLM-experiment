import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepReturn YangMills.Construction.WeightedResponses
structure ParameterFacts (Λ : MomentParameters) : Prop where
  assignment_admissible : Λ.table.Admissible
  coldStep : Λ.table.ColdStepHolds
  coldRegime : Λ.table.HoldsFrom ColdRegimeEstimatesAt
  floorMin_le : Λ.table.floorMin ≤ Λ.floor
  returns : ExpansionReturnsAt (Λ.table.stepParameters Λ.floor)
  response_admissible : ∀ y : ℝ, Λ.response.Admissible (Λ.table.stepParameters y)
  two_le : 2 ≤ Λ.k
def parameterStatementsCombine : Prop :=
  (∀ P Q : MomentParameters → Prop, ForAllParameters P → ForAllParameters Q → ForAllParameters fun Λ => P Λ ∧ Q Λ) ∧
  (∀ P Q : MomentParameters → Prop, (∀ Λ, ParameterFacts Λ → P Λ → Q Λ) → ForAllParameters P → ForAllParameters Q) ∧
  (∀ P : ParameterAssignment → ℝ → Prop, YangMills.Construction.ResponseInTheExpansion.HoldsOnParameterFamilies P →
    ForAllParameters fun Λ => P Λ.table Λ.floor) ∧
  ForAllParameters ParameterFacts
end YangMills.Construction.MomentLaw
end
