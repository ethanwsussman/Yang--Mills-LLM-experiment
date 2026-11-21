import YangMills.Construction.Continuum.ConditionsOnASequenceOfFunctionalsOnFlatSpaces
import YangMills.Construction.Continuum.SchwartzTestsAndMollifiers
import Reconstruction.MinkowskiSpace.FunctionsOfABoundedFieldForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FieldForms
open ProjectionMeasures OneLoopNotation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def IsEuclidean (E : FourBorelSet → BddOp H) (Ω : H) (A : ℝ → BddOp H) : Prop :=
  ∀ (m : ℕ) (x : TestSpaces.PointTuple (m + 1)), x ∈ TestSpaces.increasingTimes (m + 1) →
    ∀ (R : Matrix.orthogonalGroup (Fin 4) ℝ) (perm : Equiv.Perm (Fin (m + 1))),
      TestSpaces.rotatePermute R perm x ∈ TestSpaces.increasingTimes (m + 1) →
        orderedSchwinger E Ω A m (TestSpaces.rotatePermute R perm x) =
          orderedSchwinger E Ω A m x
def orderedIntegral (E : FourBorelSet → BddOp H) (Ω : H) (A : ℝ → BddOp H) (m : ℕ)
    (φ : TestSpaces.PointTuple (m + 1) → ℂ) : ℂ :=
  ∫ x, (TestSpaces.increasingTimes (m + 1)).indicator
    (fun y => φ y * orderedSchwinger E Ω A m y) x
def RepresentsFunctional (E : FourBorelSet → BddOp H) (Ω : H) (A : ℝ → BddOp H)
    (sigma : TestSpaces.SepTuple → ℝ) : Prop :=
  TestSpaces.IsSepFunctional sigma ∧
    ∀ (m : ℕ) (X : TestSpaces.SepTupleOfCard (m + 1)), WightmanReconstruction.IsTimeOrdered X.1 →
      ((sigma ⟨m + 1, X⟩ : ℝ) : ℂ) =
        orderedIntegral E Ω A m (TestSpaces.tensorProdComplex X.1)
def RepresentsSequence (E : FourBorelSet → BddOp H) (Ω : H) (A : ℝ → BddOp H)
    (S : ConfigSpace.FlatSequence) : Prop :=
  ConfigSpace.IsLinearFunctionalSeq S ∧
    ∀ (m : ℕ) (φ : TestSpaces.PointTuple (m + 1) → ℂ),
      φ ∈ (TestSpaces.smoothCompactSupp (TestSpaces.increasingTimes (m + 1)) :
        Set (TestSpaces.PointTuple (m + 1) → ℂ)) →
      ∀ h : φ ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
        S.atSucc m ⟨φ, h⟩ = orderedIntegral E Ω A m φ
end YangMills.Construction.FieldForms
