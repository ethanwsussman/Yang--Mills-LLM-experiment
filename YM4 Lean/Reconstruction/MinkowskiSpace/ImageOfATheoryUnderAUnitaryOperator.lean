import Reconstruction.MinkowskiSpace.TheoriesOfASequenceImagesOfTheoriesAndTheOperatorOfAForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MinkowskiSpace
open FieldForms ConfigSpace ProjectionMeasures FormsOperators OneLoopNotation ComplexHilbert
  WightmanTheory FieldFormHilbert FormReconstruction
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
structure UnitaryImageProperties (L : UnitaryMap H H') (T : HermitianScalarTheory H)
    (T' : HermitianScalarTheory H') : Prop where
  isUnitaryImage : IsUnitaryImage L T T'
  isTheoryOf_image : ∀ S : FlatSequence, IsTheoryOf T S → IsTheoryOf T' S
  energyMomentum_image : ∀ F : FourBorelSet → BddOp H, T.IsEnergyMomentumMeasure F →
    ∃ F' : FourBorelSet → BddOp H', T'.IsEnergyMomentumMeasure F' ∧
      ∀ (t : ℝ) (ψ : H), 0 ≤ t → HermitianScalarTheory.hamiltonianSemigroup F' t (L ψ) =
        L (HermitianScalarTheory.hamiltonianSemigroup F t ψ)
def UnitaryImageExists : Prop :=
  ∀ {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (L : UnitaryMap H H') (T : HermitianScalarTheory H),
    ∃ T' : HermitianScalarTheory H', UnitaryImageProperties L T T'
end YangMills.Construction.MinkowskiSpace
end
