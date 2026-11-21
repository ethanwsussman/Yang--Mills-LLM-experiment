import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
def SmoothSeqStateMemTensorHilbert : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
      (W : ℝ → OneLoopNotation.BddOp H) (m c : ℝ),
      FieldForms.IsBoundedFieldForm P Ω W m c →
      ∀ F : ConfigSpace.AdmissibleSeq, FormReconstruction.IsSmoothPositiveTimeSeq F →
        (∀ n : ℕ, ProjectionMeasures.HasWeakIntegrandData
          (tsupport (FormReconstruction.succMember F n))
          (FormReconstruction.wickStateAt P Ω W n) (FormReconstruction.succMember F n)) ∧
        FormReconstruction.smoothSeqState P Ω W F ∈ FieldFormHilbert.tensorHilbert P Ω W
end YangMills.Construction.MinkowskiSpace
end
