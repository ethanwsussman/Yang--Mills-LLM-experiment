import YangMills.Construction.FourPointCondition.FourPointFunctionDefs
import YangMills.Construction.ParameterData.ScaleSequenceData
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def lawsAtFlowDataAt (ℓ : TorusLumps.StepParameters) (ys lr c₅ : ℝ) (al : ℝ → ℕ → ℝ) : Prop :=
  ∀ Bs lam : ℝ, 2 * ℓ.B ≤ Bs → 0 < lam → lam ≤ lr → ∀ vt : ℝ, 0 < vt → vt ≤ 1 →
    ∀ g : ℝ, 0 < g → ys ≤ g ^ (-2 : ℤ) → ∀ room : ℕ → ℝ, RoomFunctions.IsSubexpGrowth room →
      ∃ (d₀ : ℝ) (ηBar εBar : ℝ → ℝ),
        EvaluationLaws (flowProfile ℓ g Bs room al) ℓ.side vt lam (lam + c₅) d₀ 1 ∧
        SharpEvaluationLaws (flowProfile ℓ g Bs room al) ℓ.side vt d₀ 1 ηBar (fun _ => εBar) ∧
        ∀ K₀ : ℕ, ∃ (K : ℕ+) (β : ℝ), K₀ < (K : ℕ) ∧ (flowProfile ℓ g Bs room al).IsFirstPassage K β
def HasTrajectoryDataForAllShifts {T : RenormalizationStepParameters.ParameterAssignment} {y : ℝ}
    (D : TrajectoryData.TrajectoryParameters T y) : Prop :=
  ∀ Bs lam : ℝ, 2 * T.B ≤ Bs → 0 < lam → lam ≤ D.rateBound →
    (D.withShift Bs lam).Admissible ∧ TrajectoryData.HasTrajectoryData (D.withShift Bs lam)
def lawsAtFlowDataStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∃ Kr : WeightedResponses.ResponseParameters,
    Kr.Admissible (Tb.stepParameters y) ∧
    ∀ D : TrajectoryData.TrajectoryParameters Tb y, HasTrajectoryDataForAllShifts D → ∃ al : ℝ → ℕ → ℝ,
      (∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, D.floorStar ≤ (TorusLumps.couplingFlow (Tb.stepParameters y) β j).1) →
        ResponseInTheExpansion.IsChainResponseCoeff (Tb.stepParameters y) Kr β k (al β)) ∧
      lawsAtFlowDataAt (Tb.stepParameters y) D.floorStar D.rateBound D.c₅ al
end YangMills.Construction.FourPointCondition
end
