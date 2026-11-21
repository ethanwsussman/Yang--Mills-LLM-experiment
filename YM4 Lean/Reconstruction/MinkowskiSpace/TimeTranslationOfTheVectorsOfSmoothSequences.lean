import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
def SmoothSeqStateTimeShift : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
      (W : ℝ → OneLoopNotation.BddOp H) (m c : ℝ),
      FieldForms.IsBoundedFieldForm P Ω W m c →
      ∀ F : ConfigSpace.AdmissibleSeq, FormReconstruction.IsSmoothPositiveTimeSeq F →
        ∀ s : ℝ, 0 ≤ s →
        ∃ G : ConfigSpace.AdmissibleSeq,
          ConfigSpace.seqValues G = ConfigSpace.timeShift s (ConfigSpace.seqValues F) ∧
            FormReconstruction.IsSmoothPositiveTimeSeq G ∧
            FormReconstruction.smoothSeqState P Ω W G =
              FieldForms.spectralTranslation P (FieldForms.imagTimeShift s)
                (FormReconstruction.smoothSeqState P Ω W F)
end YangMills.Construction.MinkowskiSpace
end
