import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction
open FormsOperators (IsHilbertCompletion IsContractive IsPositiveBounded IsSelfAdj
  IsC0Semigroup formRadical ofCLM formOnQuotient)
namespace PositiveFormReconstruction.SemigroupOnCompletion
def TransferSemigroupSpec : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D : PreHilbertData V) (h : D.IsAdmissible)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : (V ⧸ formRadical D.form h.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
    IsHilbertCompletion (formOnQuotient D.form h.hermitian.toIsSesquilinear) e →
    let hs := h.hermitian.toIsSesquilinear
    (∀ t, CLMExtends D hs e (D.semigroupMap t) (transferOp D hs e t)) ∧
    IsC0Semigroup (transferOp D hs e) ∧
    (∀ t, IsPositiveBounded (transferOp D hs e t) ∧
      IsSelfAdj (ofCLM (transferOp D hs e t)) ∧
      IsContractive (transferOp D hs e t)) ∧
    ∀ t, transferOp D hs e t (vacuum D hs e) = vacuum D hs e
end PositiveFormReconstruction.SemigroupOnCompletion
end YangMills.Construction
