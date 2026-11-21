import YangMills.Construction.HilbertSpaces.ReconstructionFromAPositiveFormDefs
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped NNReal ComplexOrder InnerProductSpace
noncomputable section
namespace YangMills.Construction
open EuclideanBorel (Space)
open FormsOperators (IsHilbertCompletion IsStronglyContUnitaryRep IsUnitaryRep
  formRadical ofCLM formOnQuotient)
namespace PositiveFormReconstruction.UnitaryOpsOnCompletion
def UnitaryActionSpec : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (D : PreHilbertData V) (h : D.IsAdmissible)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : (V ⧸ formRadical D.form h.hermitian.toIsSesquilinear) →ₗ[ℂ] H),
    IsHilbertCompletion (formOnQuotient D.form h.hermitian.toIsSesquilinear) e →
    let hs := h.hermitian.toIsSesquilinear
    (∀ a, UnitaryExtends D hs e (D.translationMap a) (translationOp D hs e a)) ∧
    IsStronglyContUnitaryRep (translationOp D hs e) ∧
    (∀ a, translationOp D hs e a (vacuum D hs e) = vacuum D hs e) ∧
    (∀ a t, toCLM (translationOp D hs e a) * transferOp D hs e t =
      transferOp D hs e t * toCLM (translationOp D hs e a)) ∧
    (∀ g, UnitaryExtends D hs e (D.rotationMap g) (rotationOp D hs e g)) ∧
    IsUnitaryRep (rotationOp D hs e) ∧
    (∀ g, rotationOp D hs e g (vacuum D hs e) = vacuum D hs e) ∧
    (∀ g t, toCLM (rotationOp D hs e g) * transferOp D hs e t =
      transferOp D hs e t * toCLM (rotationOp D hs e g)) ∧
    (∀ g a, toCLM (rotationOp D hs e g) * toCLM (translationOp D hs e a) =
      toCLM (translationOp D hs e (rotateSpatial g a)) * toCLM (rotationOp D hs e g)) ∧
    ∀ g a, FormsOperators.unitaryConjugate (rotationOp D hs e g)
        (ofCLM (toCLM (translationOp D hs e a))) =
      ofCLM (toCLM (translationOp D hs e (rotateSpatial g a)))
end PositiveFormReconstruction.UnitaryOpsOnCompletion
end YangMills.Construction
