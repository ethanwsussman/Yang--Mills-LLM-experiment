import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open YangMills.Construction.FormsOperators (IsHilbertCompletion formRadical formOnQuotient)
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.ClusteringVacuumKernel
def Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D : PreHilbertData V) (hD : D.IsAdmissible)
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ι : (V ⧸ formRadical D.form hD.hermitian.toIsSesquilinear) →ₗ[ℂ] E),
    IsHilbertCompletion (formOnQuotient D.form hD.hermitian.toIsSesquilinear) ι →
    KerEqVacuumLine D hD.hermitian.toIsSesquilinear ι
end YangMills.Construction.PositiveFormReconstruction.ClusteringVacuumKernel
