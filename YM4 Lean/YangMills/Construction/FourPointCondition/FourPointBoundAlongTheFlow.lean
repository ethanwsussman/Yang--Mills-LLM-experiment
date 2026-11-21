import YangMills.Construction.FourPointCondition.LawsAtTheDataOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
open Filter Set
namespace YangMills.Construction.FourPointCondition
def FourPointConditionAtFlowData (ℓ : TorusLumps.StepParameters) (Bs g : ℝ) : Prop :=
  (∀ K₀ : ℕ, ∃ (K : ℕ) (β : ℝ), K₀ < K ∧
    β ∈ SequencePassage.passageWindow Bs g (fun b k => (TorusLumps.couplingFlow ℓ b k).1) K) ∧
  ∀ vt : ℝ, 0 < vt → vt ≤ 1 → ∀ room : ℕ → ℝ, RoomFunctions.IsSubexpGrowth room →
    ∃ d₄ : ℝ, 0 < d₄ ∧ ∀ al : ℝ → ℕ → ℝ, FourPointConditionHolds (flowProfile ℓ g Bs room al) ℓ.side vt d₄ 1
def fourPointBoundAtFlowDataStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies fun Tb y => ∀ D : TrajectoryData.TrajectoryParameters Tb y, HasTrajectoryDataForAllShifts D →
    ∀ Bs : ℝ, 2 * Tb.B ≤ Bs → ∀ g : ℝ, 0 < g → D.floorStar ≤ g ^ (-2 : ℤ) →
      FourPointConditionAtFlowData (Tb.stepParameters y) Bs g
end YangMills.Construction.FourPointCondition
end
