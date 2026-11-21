import YangMills.Construction.SystemOfAdmissibleConstants.AdmissibleSideLengths
import YangMills.Construction.SystemOfAdmissibleConstants.ConditionsOnTheAdmissibleConstants
import YangMills.Construction.SystemOfAdmissibleConstants.NumbersAreASystem
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemOfAdmissibleConstants
def FamilyBoundsAlongFlow : Prop :=
  ForAllTrajectoryCouplings fun T y D g =>
    ∃ A b : ℝ, 1 ≤ A ∧ 1 ≤ b ∧
      (∀ M : ℝ, 1 ≤ M →
        AdmissibleConstants.ClusterConditions T.side M (fun K β => β ∈ D.passageWindow K g) A b) ∧
      ∀ S : BlockExponents, CouplingFlow.FamilyBoundsHold T.side (blockCubeSize T S)
        (admissibleSides D S g) (fun K β => β ∈ D.passageWindow K g)
        (AdmissibleConstants.constantFamiliesOfBounds T.side A b)
end YangMills.Construction.SystemOfAdmissibleConstants
end
