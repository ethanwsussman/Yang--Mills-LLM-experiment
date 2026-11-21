import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
open YangMills.Construction.FormsOperators (IsHilbertCompletion formRadical formOnQuotient)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.QuotientCompletion
def Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D : PreHilbertData V) (hD : D.IsAdmissible),
    QuotientInnerProduct D hD.hermitian.toIsSesquilinear ∧
    SemigroupMapsContract D hD.hermitian.toIsSesquilinear ∧
    (∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (ι : (V ⧸ formRadical D.form hD.hermitian.toIsSesquilinear) →ₗ[ℂ] E),
      IsHilbertCompletion (formOnQuotient D.form hD.hermitian.toIsSesquilinear) ι) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (ι : (V ⧸ formRadical D.form hD.hermitian.toIsSesquilinear) →ₗ[ℂ] E),
      IsHilbertCompletion (formOnQuotient D.form hD.hermitian.toIsSesquilinear) ι →
      VacuumNormSeparable D hD.hermitian.toIsSesquilinear ι
end YangMills.Construction.PositiveFormReconstruction.QuotientCompletion
