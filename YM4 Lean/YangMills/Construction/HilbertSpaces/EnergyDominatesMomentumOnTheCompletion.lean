import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound
open YangMills.Construction.FormsOperators (IsHilbertCompletion formRadical formOnQuotient)
def Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : PreHilbertData V) (hS : S.IsAdmissible)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (j : (V ⧸ formRadical S.form hS.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
    IsHilbertCompletion (formOnQuotient S.form hS.hermitian.toIsSesquilinear) j →
    EnergyBoundsMomentum S hS.hermitian.toIsSesquilinear j
end YangMills.Construction.PositiveFormReconstruction.CompletionEnergyBound
end
