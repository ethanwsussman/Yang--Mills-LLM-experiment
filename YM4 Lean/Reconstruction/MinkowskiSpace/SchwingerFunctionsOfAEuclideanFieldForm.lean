import YangMills.Construction.Coordinates.HolomorphyInCoordinates
import Reconstruction.MinkowskiSpace.EuclideanFieldFormsAndWhatAFormRepresents
import Mathlib
set_option autoImplicit false
open ComplexConjugate
noncomputable section
namespace YangMills.Construction.FieldForms
def realPartPoint (m : ℕ) (z : Coordinates.ComplexCoordinates ((m + 1) * 4)) :
    TestSpaces.PointTuple (m + 1) :=
  fun i c => (z (finProdFinEquiv (i, c))).re
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open Classical in
def schwinger (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (v : H)
    (B : ℝ → OneLoopNotation.BddOp H) (m : ℕ) (x : TestSpaces.PointTuple (m + 1)) : ℂ :=
  if h : ∃ p : Matrix.orthogonalGroup (Fin 4) ℝ × Equiv.Perm (Fin (m + 1)),
      TestSpaces.rotatePermute p.1 p.2 x ∈ TestSpaces.increasingTimes (m + 1) then
    FieldForms.orderedSchwinger P v B m
      (TestSpaces.rotatePermute h.choose.1 h.choose.2 x)
  else 0
def integralSchwinger (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (v : H)
    (B : ℝ → OneLoopNotation.BddOp H) (m : ℕ) (f : TestSpaces.PointTuple (m + 1) → ℂ) : ℂ :=
  ∫ x, (TestSpaces.distinctLocus (m + 1)).indicator
    (fun y => f y * schwinger P v B m y) x
def SchwingerWellDefined (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (v : H)
    (B : ℝ → OneLoopNotation.BddOp H) (m : ℕ) : Prop :=
  ∀ x ∈ TestSpaces.distinctLocus (m + 1),
    (∃ (R : Matrix.orthogonalGroup (Fin 4) ℝ) (s : Equiv.Perm (Fin (m + 1))),
      (R : Matrix (Fin 4) (Fin 4) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ ∧
        TestSpaces.rotatePermute R s x ∈ TestSpaces.increasingTimes (m + 1)) ∧
    ∀ (R : Matrix.orthogonalGroup (Fin 4) ℝ) (s : Equiv.Perm (Fin (m + 1))),
      TestSpaces.rotatePermute R s x ∈ TestSpaces.increasingTimes (m + 1) →
        schwinger P v B m x =
          FieldForms.orderedSchwinger P v B m (TestSpaces.rotatePermute R s x)
def SchwingerAnalyticInvariant (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H)
    (v : H) (B : ℝ → OneLoopNotation.BddOp H) (m : ℕ) : Prop :=
  Coordinates.ComplexCoordinates.IsRealAnalyticIn (N' := 1)
      {z | z ∈ Coordinates.ComplexCoordinates.realLocus ((m + 1) * 4) ∧
        realPartPoint m z ∈ TestSpaces.distinctLocus (m + 1)}
      (fun z _ => schwinger P v B m (realPartPoint m z)) ∧
    (∀ x ∈ TestSpaces.increasingTimes (m + 1),
      schwinger P v B m x = FieldForms.orderedSchwinger P v B m x) ∧
    ∀ (r : Motions.RigidMotion) (s : Equiv.Perm (Fin (m + 1))),
      ∀ x ∈ TestSpaces.distinctLocus (m + 1),
        schwinger P v B m (fun i => r.toFun (x (s i))) = schwinger P v B m x
def SequenceEqIntegralSchwinger (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H)
    (v : H) (B : ℝ → OneLoopNotation.BddOp H) (m : ℕ) : Prop :=
  ∀ S : ConfigSpace.FlatSequence, FieldForms.RepresentsSequence P v B S →
    (∀ (f : ConfigSpace.schwartzFlatOffDiagonal (m + 1))
      (R : Matrix.orthogonalGroup (Fin 4) ℝ)
      (h : Motions.actOnFun ⟨R.1, R.2, 0⟩ f.1 ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1)),
      S.atSucc m ⟨_, h⟩ = S.atSucc m f) →
    (∀ (f : ConfigSpace.schwartzFlatOffDiagonal (m + 1))
      (s : Equiv.Perm (Fin (m + 1)))
      (h : Motions.permuteArgs s f.1 ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1)),
      S.atSucc m ⟨_, h⟩ = S.atSucc m f) →
    ∀ f : TestSpaces.PointTuple (m + 1) → ℂ,
      f ∈ (TestSpaces.smoothCompactSupp (TestSpaces.distinctLocus (m + 1)) :
        Set (TestSpaces.PointTuple (m + 1) → ℂ)) →
      ∀ h : f ∈ ConfigSpace.schwartzFlatOffDiagonal (m + 1),
        S.atSucc m ⟨f, h⟩ = integralSchwinger P v B m f
def FunctionalEqIntegralSchwinger (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H)
    (v : H) (B : ℝ → OneLoopNotation.BddOp H) (m : ℕ) : Prop :=
  ∀ F : TestSpaces.SepTuple → ℝ, FieldForms.RepresentsFunctional P v B F →
    WightmanReconstruction.IsPermutationInvariant F →
    (∀ R : Matrix.orthogonalGroup (Fin 4) ℝ,
      WightmanReconstruction.IsMotionInvariant F ⟨R.1, R.2, 0⟩) →
    ∀ X : TestSpaces.SepTupleOfCard (m + 1),
      ((F ⟨m + 1, X⟩ : ℝ) : ℂ) =
        integralSchwinger P v B m (TestSpaces.tensorProdComplex X.1)
def EuclideanSchwingerProperties : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ProjectionMeasures.FourBorelSet → OneLoopNotation.BddOp H) (v : H)
    (B : ℝ → OneLoopNotation.BddOp H) (p C : ℝ),
    FieldForms.IsBoundedFieldForm P v B p C → FieldForms.IsEuclidean P v B → ∀ m : ℕ,
      SchwingerWellDefined P v B m ∧
      SchwingerAnalyticInvariant P v B m ∧
      (∀ x ∈ TestSpaces.distinctLocus (m + 1),
        conj (schwinger P v B m x) = schwinger P v B m x) ∧
      SequenceEqIntegralSchwinger P v B m ∧
      FunctionalEqIntegralSchwinger P v B m
end YangMills.Construction.FieldForms
