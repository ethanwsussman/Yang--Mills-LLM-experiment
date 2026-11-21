import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction
open YangMills.Construction.FormsOperators (IsHilbertCompletion formRadical formOnQuotient)
def ReconstructionStatement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D : PreHilbertData V) (hD : D.IsAdmissible),
    QuotientInnerProduct D hD.hermitian.toIsSesquilinear ∧
    SemigroupMapsContract D hD.hermitian.toIsSesquilinear ∧
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (j : (V ⧸ formRadical D.form hD.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
      IsHilbertCompletion (formOnQuotient D.form hD.hermitian.toIsSesquilinear) j) ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (j : (V ⧸ formRadical D.form hD.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
      IsHilbertCompletion (formOnQuotient D.form hD.hermitian.toIsSesquilinear) j →
      VacuumNormSeparable D hD.hermitian.toIsSesquilinear j ∧
      TransferSemigroupCondition D hD.hermitian.toIsSesquilinear j ∧
      TranslationCondition D hD.hermitian.toIsSesquilinear j ∧
      RotationUnitarity D hD.hermitian.toIsSesquilinear j ∧
      EnergyBoundsMomentum D hD.hermitian.toIsSesquilinear j ∧
      KerEqVacuumLine D hD.hermitian.toIsSesquilinear j
end YangMills.Construction.PositiveFormReconstruction
