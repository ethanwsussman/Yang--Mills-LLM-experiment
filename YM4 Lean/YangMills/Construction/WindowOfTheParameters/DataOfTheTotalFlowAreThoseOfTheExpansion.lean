import YangMills.Construction.WindowOfTheParameters.FirstPassageOfASequenceForm
import YangMills.Construction.WindowOfTheParameters.FlowAboveAFloor
import YangMills.Construction.WindowOfTheParameters.FlowOfTheTotalDensities
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensityFlow
open RenormalizationStepParameters FloorBounds SequencePassage TorusLumps
def PassageWindowEqExpansionWindow : Prop :=
  ∀ (T : ParameterAssignment) (y c X : ℝ), T.Admissible → FlowAboveFloor T y c X →
    ∀ B g : ℝ, 0 ≤ B → 0 < g → X ≤ g ^ (-2 : ℤ) → ∀ K : ℕ,
      definedPassageWindow (IsDefinedUpTo (T.stepParameters y)) B g (coupling (T.stepParameters y)) K =
          SequencePassage.passageWindow B g (fun β k => (couplingFlow (T.stepParameters y) β k).1) K ∧
        ∀ β ∈ SequencePassage.passageWindow B g (fun β k => (couplingFlow (T.stepParameters y) β k).1) K, ∀ k ≤ K,
          coupling (T.stepParameters y) β k = (couplingFlow (T.stepParameters y) β k).1
end YangMills.Construction.TotalDensityFlow
end
