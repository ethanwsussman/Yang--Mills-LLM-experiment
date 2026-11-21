import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open scoped InnerProductSpace in
def SmoothSeqStatesTotal : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (Ω : H)
      (W : ℝ → OneLoopNotation.BddOp H) (m c : ℝ),
      FieldForms.IsBoundedFieldForm P Ω W m c →
      ∀ v : H, v ∈ FieldFormHilbert.tensorHilbert P Ω W →
        (∀ F : ConfigSpace.AdmissibleSeq, FormReconstruction.IsSmoothPositiveTimeSeq F →
          ⟪v, FormReconstruction.smoothSeqState P Ω W F⟫_ℂ = 0) → v = 0
end YangMills.Construction.MinkowskiSpace
end
